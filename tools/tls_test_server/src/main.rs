use std::io::{Read, Write};
use std::net::TcpListener;
use std::sync::Arc;

fn main() {
    let port: u16 = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(4433);

    if let Err(e) = run_server(port) {
        eprintln!("[SERVER FAIL: {}]", e);
        std::process::exit(1);
    }
}

fn run_server(port: u16) -> Result<(), Box<dyn std::error::Error>> {
    // Generate self-signed Ed25519 certificate via rcgen 0.13
    let key_pair = rcgen::KeyPair::generate_for(&rcgen::PKCS_ED25519)?;
    let params = rcgen::CertificateParams::new(vec!["localhost".to_string()])?;
    let cert = params.self_signed(&key_pair)?;
    let cert_der = rustls::pki_types::CertificateDer::from(cert.der().to_vec());
    let key_der = rustls::pki_types::PrivateKeyDer::Pkcs8(
        rustls::pki_types::PrivatePkcs8KeyDer::from(key_pair.serialize_der()),
    );

    // Configure rustls with TLS 1.3 only
    let provider = Arc::new(rustls::crypto::ring::default_provider());
    let config = rustls::ServerConfig::builder_with_provider(provider)
        .with_protocol_versions(&[&rustls::version::TLS13])?
        .with_no_client_auth()
        .with_single_cert(vec![cert_der], key_der)?;
    let config = Arc::new(config);

    let addr = format!("0.0.0.0:{}", port);
    let listener = TcpListener::bind(&addr)?;
    eprintln!("Listening on {}", addr);

    // Accept one connection
    let (mut stream, peer) = listener.accept()?;
    eprintln!("Connection from {}", peer);

    let mut conn = rustls::ServerConnection::new(config)?;
    let mut tls = rustls::Stream::new(&mut conn, &mut stream);

    // Send greeting
    tls.write_all(b"Hello from rustls TLS 1.3\n")?;
    tls.flush()?;

    // Read client response
    let mut buf = vec![0u8; 4096];
    let n = tls.read(&mut buf).unwrap_or(0);
    if n > 0 {
        let response = String::from_utf8_lossy(&buf[..n]);
        eprintln!("Client said: {}", response.trim());
    }

    println!("[SERVER OK]");
    Ok(())
}
