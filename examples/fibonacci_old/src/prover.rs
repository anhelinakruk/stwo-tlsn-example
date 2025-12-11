use std::net::SocketAddr;

use http_body_util::Empty;
use hyper::{body::Bytes, header, Request, StatusCode, Uri};
use hyper_util::rt::TokioIo;
use spansy::{
    http::{BodyContent, Responses},
    Spanned,
};
use tlsn::{
    config::{CertificateDer, ProtocolConfig, RootCertStore}, connection::ServerName, hash::HashAlgId, prover::{ProveConfig, ProveConfigBuilder, Prover, ProverConfig, TlsConfig}, transcript::{
        TranscriptCommitConfig, TranscriptCommitConfigBuilder, TranscriptCommitmentKind,
    }
};
use tokio::io::{AsyncRead, AsyncWrite, AsyncWriteExt};
use tokio_util::compat::{FuturesAsyncReadCompatExt, TokioAsyncReadCompatExt};
use tracing::instrument;

use crate::types::{extract_fibonacci_index, received_commitments, received_secrets, verify_fibonacci_index_commitment};

pub static CA_CERT_DER: &[u8] = include_bytes!("certs/rootCA.der");
const MAX_SENT_DATA: usize = 1 << 12;
const MAX_RECV_DATA: usize = 1 << 14;

#[instrument(skip(verifier_socket, verifier_extra_socket))]
pub async fn prover<T: AsyncWrite + AsyncRead + Send + Unpin + 'static>(
    verifier_socket: T,
    mut verifier_extra_socket: T,
    server_addr: &SocketAddr,
    uri: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let uri = uri.parse::<Uri>()?;

    if uri.scheme().map(|s| s.as_str()) != Some("https") {
        return Err("URI must use HTTPS scheme".into());
    }

    let server_domain = uri.authority().ok_or("URI must have authority")?.host();

    let mut tls_config_builder = TlsConfig::builder();
    tls_config_builder.root_store(RootCertStore {
        roots: vec![CertificateDer(CA_CERT_DER.to_vec())],
    });
    let tls_config = tls_config_builder.build()?;

    let mut prover_config_builder = ProverConfig::builder();
    prover_config_builder
        .server_name(ServerName::Dns(server_domain.try_into()?))
        .tls_config(tls_config)
        .protocol_config(
            ProtocolConfig::builder()
                .max_sent_data(MAX_SENT_DATA)
                .max_recv_data(MAX_RECV_DATA)
                .build()?,
        );

    let prover_config = prover_config_builder.build()?;

    // Create prover and connect to verifier
    // Perform the setup phase with the verifier
    let prover = Prover::new(prover_config)
        .setup(verifier_socket.compat())
        .await?;

    // Connect to TLS Server
    let tls_client_socket = tokio::net::TcpStream::connect(server_addr).await?;

    // Pass server connection into the prover
    let (mpc_tls_connection, prover_fut) = prover.connect(tls_client_socket.compat()).await?;

    // Wrap the connection in a TokioIo compatibility layer to use it with hyper
    let mpc_tls_connection = TokioIo::new(mpc_tls_connection.compat());

    // Spawn the Prover to run in the background
    let prover_task = tokio::spawn(prover_fut);

    // MPC-TLS Handshake
    let (mut request_sender, connection) =
        hyper::client::conn::http1::handshake(mpc_tls_connection).await?;

    // Spawn the connection to run in the background
    tokio::spawn(connection);

    // MPC-TLS: Send Request and wait for Response
    let request = Request::builder()
        .uri(uri.clone())
        .header("Host", server_domain)
        .header("Connection", "close")
        .header(header::AUTHORIZATION, "Bearer random_auth_token")
        .method("GET")
        .body(Empty::<Bytes>::new())?;

    let response = request_sender.send_request(request).await?;

    if response.status() != StatusCode::OK {
        return Err(format!("MPC-TLS request failed with status {}", response.status()).into());
    }

    // Create proof for the Verifier
    let mut prover = prover_task.await??;

    let transcript = prover.transcript().clone();
    let mut prove_config_builder = ProveConfig::builder(&transcript);

    // Reveal the DNS name
    prove_config_builder.server_identity();

     let sent: &[u8] = transcript.sent();
    let received: &[u8] = transcript.received();
    let sent_len = sent.len();
    let recv_len = received.len();
    tracing::info!("Sent length: {}, Received length: {}", sent_len, recv_len);

    // Reveal the entire HTTP request except for the authorization bearer token
    reveal_request(sent, &mut prove_config_builder)?;

    let mut transcript_commitment_builder = TranscriptCommitConfig::builder(&transcript);
    transcript_commitment_builder.default_kind(TranscriptCommitmentKind::Hash {
        alg: HashAlgId::BLAKE3,
    });

    reveal_received(
        received,
        &mut prove_config_builder,
        &mut transcript_commitment_builder,
    )?;

    let transcripts_commitment_config = transcript_commitment_builder.build()?;
    prove_config_builder.transcript_commit(transcripts_commitment_config);

    let prove_config = prove_config_builder.build()?;

    // MPC-TLS prove
    let prover_output = prover.prove(&prove_config).await?;
    prover.close().await?;

    // Generate ZK proof that fibonacci(secret_index) = computed_value
    let received_commitment = received_commitments(&prover_output.transcript_commitments);

    let received_secret = received_secrets(&prover_output.transcript_secrets);

    let fibonacci_index = extract_fibonacci_index(received)?;

    verify_fibonacci_index_commitment(
        fibonacci_index,
        received_commitment[0],
        received_secret[0],
    )?;

    // Extract blinders (16 bytes each)
    let blinder: [u8; 16] = received_secret[0]
        .blinder
        .as_bytes()
        .try_into()
        .map_err(|_| "Blinder1 must be exactly 16 bytes")?;

    // TODO: Implement generate_fib_zk_proof
    // let proof_bundle = generate_fib_zk_proof(
    //     fibonacci_index,
    //     received_commitment,
    //     &blinder,
    // )?;
    let proof_bundle = crate::types::FibZKProofBundle {
        target_element_computing: fibonacci_index,
        proof: vec![],
        statement: vec![],
    };

    // Send zk proof bundle to verifier
    let serialized_proof = bincode::serialize(&proof_bundle)?;
    verifier_extra_socket.write_all(&serialized_proof).await?;
    verifier_extra_socket.shutdown().await?;

    Ok(())
}

// Reveal everything from the request, except for the authorization token
fn reveal_request(
    request: &[u8],
    builder: &mut ProveConfigBuilder<'_>,
) -> Result<(), Box<dyn std::error::Error>> {
    use spansy::http::Requests;

    let reqs = Requests::new_from_slice(request).collect::<Result<Vec<_>, _>>()?;

    let req = reqs.first().ok_or("No requests found")?;

    if req.request.method.as_str() != "GET" {
        return Err(format!("Expected GET method, found {}", req.request.method.as_str()).into());
    }

    let authorization_header = req
        .headers_with_name(header::AUTHORIZATION.as_str())
        .next()
        .ok_or("Authorization header not found")?;

    let start_pos = authorization_header
        .span()
        .indices()
        .min()
        .ok_or("Could not find authorization header start position")?
        + header::AUTHORIZATION.as_str().len()
        + 2;
    let end_pos =
        start_pos + authorization_header.span().len() - header::AUTHORIZATION.as_str().len() - 2;

    builder.reveal_sent(&(0..start_pos))?;
    builder.reveal_sent(&(end_pos..request.len()))?;

    Ok(())
}

fn reveal_received(
    received: &[u8],
    builder: &mut ProveConfigBuilder<'_>,
    transcript_commitment_builder: &mut TranscriptCommitConfigBuilder,
) -> Result<(), Box<dyn std::error::Error>> {
    let resp = Responses::new_from_slice(received).collect::<Result<Vec<_>, _>>()?;

    let response = resp.first().ok_or("No responses found")?;
    let body = response.body.as_ref().ok_or("Response body not found")?;

    let BodyContent::Json(json) = &body.content else {
        return Err("Expected JSON body content".into());
    };

    // Commit to hash of both fibonacci indices (these are SECRET values from server)
    let challenge_index1 = json
        .get("challenge_index1")
        .ok_or("challenge_index1 field not found in JSON")?;
    let challenge_index2 = json
        .get("challenge_index2")
        .ok_or("challenge_index2 field not found in JSON")?;

    let start_pos1 = challenge_index1
        .span()
        .indices()
        .min()
        .ok_or("Could not find challenge_index1 start position")?;
    let end_pos1 = challenge_index1
        .span()
        .indices()
        .max()
        .ok_or("Could not find challenge_index1 end position")?
        + 1;

    let start_pos2 = challenge_index2
        .span()
        .indices()
        .min()
        .ok_or("Could not find challenge_index2 start position")?;
    let end_pos2 = challenge_index2
        .span()
        .indices()
        .max()
        .ok_or("Could not find challenge_index2 end position")?
        + 1;

    tracing::info!("Index1 as string: {:?}", String::from_utf8_lossy(&received[start_pos1..end_pos1]));
    tracing::info!("Index2 as string: {:?}", String::from_utf8_lossy(&received[start_pos2..end_pos2]));

    // Commit to both indices
    transcript_commitment_builder.commit_recv(&(start_pos1..end_pos1))?;
    transcript_commitment_builder.commit_recv(&(start_pos2..end_pos2))?;

    // Reveal the rest of the response (everything except the two indices)
    let min_start = start_pos1.min(start_pos2);
    let max_end = end_pos1.max(end_pos2);

    if min_start > 0 {
        builder.reveal_recv(&(0..min_start))?;
    }

    // Reveal between the two indices if they're not adjacent
    if start_pos1 < start_pos2 && end_pos1 < start_pos2 {
        builder.reveal_recv(&(end_pos1..start_pos2))?;
    } else if start_pos2 < start_pos1 && end_pos2 < start_pos1 {
        builder.reveal_recv(&(end_pos2..start_pos1))?;
    }

    if max_end < received.len() {
        builder.reveal_recv(&(max_end..received.len()))?;
    }

    Ok(())
}
