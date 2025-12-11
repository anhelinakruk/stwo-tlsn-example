#![feature(portable_simd)]
#![feature(array_chunks)]
#![feature(iter_array_chunks)]

use prover::prover;
use std::{
    env,
    net::{IpAddr, SocketAddr},
};
use verifier::verifier;

pub mod prover;
pub mod verifier;
pub mod fibonacci;
pub mod types;
pub mod bridge;
pub mod blake3;

#[cfg(test)]
mod bridge_fib_test;
mod blake_solo_test;
mod full_test;

const TEST_SERVER_DOMAIN: &str = "localhost";
const TEST_SERVER_PORT: u16 = 3000;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();

    let server_host: String = env::var("SERVER_HOST").unwrap_or("127.0.0.1".into());
    let server_port: u16 = env::var("SERVER_PORT")
        .map(|port| port.parse().expect("port should be valid integer"))
        .unwrap_or(TEST_SERVER_PORT);

    let server_domain = env::var("SERVER_DOMAIN").unwrap_or(TEST_SERVER_DOMAIN.to_string());

    let uri = format!("https://{}:{}/fibonacci", server_domain, server_port);
    let server_ip: IpAddr = server_host
        .parse()
        .map_err(|e| format!("Invalid IP address '{}': {}", server_host, e))?;
    let server_addr = SocketAddr::from((server_ip, server_port));
    
    tracing::info!("Server: {}", uri);
    tracing::info!("Address: {}", server_addr);

    let (prover_socket, verifier_socket) = tokio::io::duplex(1 << 23);
    let (prover_extra_socket, verifier_extra_socket) = tokio::io::duplex(1 << 23);

    let (_prover_result, transcript) = tokio::try_join!(
        prover(prover_socket, prover_extra_socket, &server_addr, &uri),
        verifier(verifier_socket, verifier_extra_socket, &server_domain)
    )?;

    println!("Successfully verified {}", &uri);

    println!(
        "Verified sent data:\n{}",
        bytes_to_redacted_string(transcript.sent_unsafe())
    );
    println!(
        "Verified received data:\n{}",
        bytes_to_redacted_string(transcript.received_unsafe())
    );

    Ok(())
}

/// Render redacted bytes as `🙈`.
pub fn bytes_to_redacted_string(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).replace('\0', "🙈")
}

