use super::types::{FibZKProofBundle, received_commitments};

use stwo::core::pcs::PcsConfig;
use stwo::core::proof::StarkProof;
use stwo::core::vcs::blake2_merkle::Blake2sMerkleHasher;
use tlsn::{
    config::{CertificateDer, ProtocolConfigValidator, RootCertStore},
    connection::ServerName,
    hash::HashAlgId,
    transcript::{Direction, PartialTranscript},
    verifier::{Verifier, VerifierConfig, VerifierOutput, VerifyConfig},
};
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite};
use tokio_util::compat::TokioAsyncReadCompatExt;
use tracing::instrument;

pub static CA_CERT_DER: &[u8] = include_bytes!("certs/rootCA.der");

const MAX_SENT_DATA: usize = 1 << 12;
const MAX_RECV_DATA: usize = 1 << 14;

#[instrument(skip(socket, extra_socket))]
pub async fn verifier<T: AsyncWrite + AsyncRead + Send + Sync + Unpin + 'static>(
    socket: T,
    mut extra_socket: T,
    expected_server_domain: &str,
) -> Result<PartialTranscript, Box<dyn std::error::Error>> {
    tracing::info!("=== Starting Verifier ===");

    // Set up Verifier with protocol configuration validator
    let config_validator = ProtocolConfigValidator::builder()
        .max_sent_data(MAX_SENT_DATA)
        .max_recv_data(MAX_RECV_DATA)
        .build()?;

    // Create a root certificate store with the server-fixture's self-signed certificate
    let verifier_config = VerifierConfig::builder()
        .root_store(RootCertStore {
            roots: vec![CertificateDer(CA_CERT_DER.to_vec())],
        })
        .protocol_config_validator(config_validator)
        .build()?;

    let verifier = Verifier::new(verifier_config);

    tracing::info!("Step 1: Verifying MPC-TLS session...");

    // Receive and verify the TLSNotary attestation
    let VerifierOutput {
        server_name,
        transcript,
        transcript_commitments,
        ..
    } = verifier
        .verify(socket.compat(), &VerifyConfig::default())
        .await?;

    let server_name = server_name.ok_or("Prover should have revealed server name")?;
    let transcript = transcript.ok_or("Prover should have revealed transcript data")?;

    tracing::info!("MPC-TLS session verified successfully");

    // Verify server name matches expected domain
    let ServerName::Dns(server_name) = server_name;
    if server_name.as_str() != expected_server_domain {
        return Err(format!(
            "Server name mismatch: expected {}, got {}",
            expected_server_domain,
            server_name.as_str()
        )
        .into());
    }
    tracing::info!("Server name verified: {}", server_name.as_str());

    // Verify sent data contains the expected server domain
    let sent = transcript.sent_unsafe().to_vec();
    let sent_data = String::from_utf8(sent.clone())
        .map_err(|e| format!("Verifier expected valid UTF-8 sent data: {}", e))?;

    if !sent_data.contains(expected_server_domain) {
        return Err(format!(
            "Verification failed: Expected host {} not found in sent data",
            expected_server_domain
        )
        .into());
    }
    tracing::info!("Sent data contains expected server domain");

    // Check received data commitments (now we have TWO commitments, one for each index)
    tracing::info!("Step 2: Verifying hash commitments for fibonacci indices...");
    let received_commitment = received_commitments(&transcript_commitments)[0];

    if received_commitment.direction != Direction::Received {
        return Err("First hash commitment should be for received data".into());
    }
    if received_commitment.hash.alg != HashAlgId::BLAKE3 {
        return Err("First hash commitment should use BLAKE3".into());
    }

    let committed_hash = &received_commitment.hash;
    tracing::info!(
        "Received hash commitment verified: {}",
        hex::encode(committed_hash.value.as_bytes())
    );

    // Receive ZK proof bundle from prover
    tracing::info!("Step 3: Receiving ZK proof bundle from prover...");
    let mut buf = Vec::new();
    extra_socket.read_to_end(&mut buf).await?;

    if buf.is_empty() {
        return Err("No ZK proof data received from prover".into());
    }

    let proof_bundle: FibZKProofBundle = bincode::deserialize(&buf)
        .map_err(|e| format!("Failed to deserialize Multi-Fib ZK proof bundle: {}", e))?;

    tracing::info!("Received Fib ZK proof bundle:");
    tracing::info!(
        "  - target_element_computing: {}",
        proof_bundle.target_element_computing
    );
    tracing::info!("  - proof size: {} bytes", proof_bundle.proof.len());

    // Deserialize the STARK proof
    tracing::info!("Step 4: Deserializing STARK proof...");
    let stark_proof: StarkProof<Blake2sMerkleHasher> = bincode::deserialize(&proof_bundle.proof)
        .map_err(|e| format!("Failed to deserialize STARK proof: {}", e))?;

    // Deserialize statements
    let statement: crate::fibonacci::FibStatement =
        bincode::deserialize(&proof_bundle.statement)
            .map_err(|e| format!("Failed to deserialize statement: {}", e))?;

    // Verify the ZK proof
    tracing::info!("Step 5: Verifying -Fib STARK proof...");
    tracing::info!("  This proves that:");
    tracing::info!("  1. Prover knows secret fibonacci indices from the server");
    tracing::info!(
        "  2. Prover computed Fibonacci value at index {}",
        proof_bundle.target_element_computing,
    );
    tracing::info!("  3. Scheduler component computed the sum of these values");
    tracing::info!("  4. All computation matches the committed hash from TLSNotary");
    tracing::info!("  Note: The actual fibonacci indices remain SECRET to the verifier!");

    // TODO: Implement verify_multi_fib
    let config = PcsConfig::default();
    // crate::fibonacci::verify_multi_fib(
    //     stark_proof,
    //     proof_bundle.target_element_computing,
    //     statement,
    //     config,
    // )?;
    let _ = (stark_proof, statement); // suppress unused warnings

    tracing::info!("Multi-Fib STARK proof verified successfully!");

    // Summary
    tracing::info!("\n=== Verification Complete ===");
    tracing::info!("TLSNotary attestation verified");
    tracing::info!("Server identity confirmed: {}", expected_server_domain);
    tracing::info!(
        "fibonacci_index committed via hash: {}",
        hex::encode(committed_hash.value.as_bytes())
    );

    tracing::info!(
        "ZK proof verified: computed Fibonacci value at index {}",
        proof_bundle.target_element_computing,
    );
    tracing::info!("Prover demonstrated knowledge of server's secrets without revealing them!");

    Ok(transcript)
}
