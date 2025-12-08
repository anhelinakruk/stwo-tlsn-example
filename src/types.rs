use serde::{Deserialize, Serialize};
use spansy::http::{BodyContent, Responses};
use spansy::Spanned;
use tlsn::hash::HashAlgId;
use tlsn::transcript::{Direction, TranscriptCommitment, TranscriptSecret, hash::{PlaintextHash, PlaintextHashSecret}};

/// Bundle containing the Multi-Fibonacci ZK proof with scheduler
#[derive(Serialize, Deserialize, Debug)]
pub struct FibZKProofBundle {
    /// Serialized STARK proof
    pub proof: Vec<u8>,
    /// Target element for first computing component
    pub target_element_computing: usize,
    /// Serialized FibStatement (log_size)
    pub statement: Vec<u8>,
}

/// Extract hash commitment for received data from transcript commitment
pub fn received_commitments(
    transcript_commitments: &[TranscriptCommitment],
) -> Vec<&PlaintextHash> {
    transcript_commitments
        .iter()
        .filter_map(|commitment| match commitment {
            TranscriptCommitment::Hash(hash) if hash.direction == Direction::Received => Some(hash),
            _ => None,
        })
        .collect()
}

/// Extract hash secrets (blinders) for received data from transcript secrets
pub fn received_secrets(transcript_secrets: &[TranscriptSecret]) -> Vec<&PlaintextHashSecret> {
    transcript_secrets
        .iter()
        .filter_map(|secret| match secret {
            TranscriptSecret::Hash(secret) if secret.direction == Direction::Received => {
                Some(secret)
            }
            _ => None,
        })
        .collect()
}

pub fn extract_fibonacci_index(
    received: &[u8],
) -> Result<usize, Box<dyn std::error::Error>> {
    let resp = Responses::new_from_slice(received).collect::<Result<Vec<_>, _>>()?;
    let response = resp.first().ok_or("No responses found")?;
    let body = response.body.as_ref().ok_or("Response body not found")?;

    let BodyContent::Json(_json) = &body.content else {
        return Err("Expected JSON body content".into());
    };

    // Find where the JSON body starts in the original bytes
    let body_start = body
        .span()
        .indices()
        .min()
        .ok_or("Could not find body start")?;
    let body_end = body
        .span()
        .indices()
        .max()
        .ok_or("Could not find body end")?
        + 1;
    let body_bytes = &received[body_start..body_end];

    // Parse the body bytes directly with serde_json
    let json_value: serde_json::Value = serde_json::from_slice(body_bytes)?;

    let index = json_value
        .get("challenge_index1")
        .and_then(|v| v.as_u64())
        .ok_or("challenge_index1 not found or not a valid u64")? as usize;

    Ok(index)
}

/// Verify that the blinded hash commitment is correct (like in interactive_zk)
/// This ensures: hash(fibonacci_index_bytes + blinder) == committed_hash
pub fn verify_fibonacci_index_commitment(
    fibonacci_index: usize,
    received_commitment: &PlaintextHash,
    received_secret: &PlaintextHashSecret,
) -> Result<(), Box<dyn std::error::Error>> {
    use tlsn::transcript::Direction;

    // Verify commitment and secret are for received data
    assert_eq!(received_commitment.direction, Direction::Received);
    assert_eq!(received_commitment.hash.alg, HashAlgId::BLAKE3);
    assert_eq!(received_secret.direction, Direction::Received);
    assert_eq!(received_secret.alg, HashAlgId::BLAKE3);

    let committed_hash = received_commitment.hash.value.as_bytes();
    let blinder = received_secret.blinder.as_bytes();

    // Convert fibonacci_index to bytes (as it appears in JSON: "5" -> b"5")
    let index_string = fibonacci_index.to_string();
    let index_bytes = index_string.as_bytes();

    tracing::info!("Verifying hash for index: {}", fibonacci_index);
    tracing::info!("  Index bytes: {:?}", index_bytes);
    tracing::info!("  Blinder: {}", hex::encode(blinder));

    // Compute hash(index_bytes + blinder) using BLAKE3
    let mut hasher = blake3::Hasher::new();
    hasher.update(index_bytes);
    hasher.update(blinder);
    let computed_hash = hasher.finalize();

    tracing::info!("  Computed hash: {}", hex::encode(computed_hash.as_bytes()));

    // Verify computed hash matches committed hash
    if committed_hash != computed_hash.as_bytes() {
        tracing::error!(
            "Hash verification failed for fibonacci_index {}",
            fibonacci_index
        );
        tracing::error!("  Expected (committed): {}", hex::encode(committed_hash));
        tracing::error!("  Computed:             {}", hex::encode(computed_hash.as_bytes()));
        return Err("Computed hash does not match committed hash".into());
    }

    tracing::info!(
        "✓ Hash commitment verified for fibonacci_index {}: {}",
        fibonacci_index,
        hex::encode(committed_hash)
    );

    Ok(())
}