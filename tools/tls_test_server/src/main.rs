use std::fs;
use std::io::{Read, Write};
use std::net::TcpListener;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use rcgen::{BasicConstraints, Certificate, CertificateParams, DnType, IsCa, KeyPair, PKCS_ED25519};
use rustls::pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer};
use rustls::server::WebPkiClientVerifier;
use rustls::{HandshakeKind, RootCertStore, ServerConfig, ServerConnection};

fn main() {
    let config_path = match parse_args(std::env::args().skip(1).collect()) {
        Ok(path) => path,
        Err(err) => {
            eprintln!("[SERVER FAIL: {}]", err);
            std::process::exit(2);
        }
    };

    let config = match Config::load(&config_path) {
        Ok(config) => config,
        Err(err) => {
            eprintln!("[SERVER FAIL: {}]", err);
            std::process::exit(2);
        }
    };

    if let Err(err) = run_server(config) {
        eprintln!("[SERVER FAIL: {}]", err);
        std::process::exit(1);
    }
}

#[derive(Clone, Debug)]
struct Config {
    listen: String,
    fixture_dir: Option<PathBuf>,
    require_client_auth: bool,
    accept_count: usize,
    greeting: String,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            listen: "127.0.0.1:4433".to_string(),
            fixture_dir: None,
            require_client_auth: false,
            accept_count: 1,
            greeting: "Hello from rustls TLS 1.3".to_string(),
        }
    }
}

fn parse_args(args: Vec<String>) -> Result<PathBuf, String> {
    if args.is_empty() {
        return Ok(PathBuf::from("tools/tls_test_server/server.sdn"));
    }

    if args.len() == 2 && args[0] == "--config" {
        return Ok(PathBuf::from(&args[1]));
    }

    if args.len() == 1 && (args[0] == "--help" || args[0] == "-h") {
        return Err("usage: tls_test_server [--config path/to/server.sdn]".to_string());
    }

    Err("usage: tls_test_server [--config path/to/server.sdn]".to_string())
}

impl Config {
    fn load(path: &Path) -> Result<Self, String> {
        let content =
            fs::read_to_string(path).map_err(|err| format!("failed to read {}: {}", path.display(), err))?;
        Self::from_sdn_text(&content)
    }

    fn from_sdn_text(content: &str) -> Result<Self, String> {
        let mut config = Self::default();
        let server_block =
            extract_block(content, "server").ok_or_else(|| "missing 'server' block".to_string())?;

        if let Some(listen) = extract_text(&server_block, "listen") {
            config.listen = listen;
        }
        if let Some(fixture_dir) = extract_text(&server_block, "fixture_dir") {
            config.fixture_dir = Some(PathBuf::from(fixture_dir));
        }
        if let Some(greeting) = extract_text(&server_block, "greeting") {
            config.greeting = greeting;
        }
        if let Some(require_client_auth) = extract_bool(&server_block, "require_client_auth") {
            config.require_client_auth = require_client_auth;
        }
        if let Some(accept_count) = extract_usize(&server_block, "accept_count") {
            if accept_count == 0 {
                return Err("server.accept_count must be greater than 0".to_string());
            }
            config.accept_count = accept_count;
        }

        Ok(config)
    }
}

fn extract_block(content: &str, key: &str) -> Option<String> {
    let marker = format!("{}:", key);
    let lines: Vec<&str> = content.lines().collect();
    for (idx, line) in lines.iter().enumerate() {
        if line.trim() == marker {
            let mut block = String::new();
            for next in lines.iter().skip(idx + 1) {
                if next.trim().is_empty() {
                    continue;
                }
                let indent = next.chars().take_while(|c| *c == ' ').count();
                if indent < 2 {
                    break;
                }
                block.push_str(next);
                block.push('\n');
            }
            return Some(block);
        }
    }
    None
}

fn extract_text(block: &str, key: &str) -> Option<String> {
    let raw = extract_scalar(block, key)?;
    Some(unquote(raw))
}

fn extract_bool(block: &str, key: &str) -> Option<bool> {
    match extract_scalar(block, key)?.trim() {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

fn extract_usize(block: &str, key: &str) -> Option<usize> {
    extract_scalar(block, key)?.trim().parse().ok()
}

fn extract_scalar(block: &str, key: &str) -> Option<String> {
    let prefix = format!("{}:", key);
    for line in block.lines() {
        let trimmed = line.trim();
        if let Some(value) = trimmed.strip_prefix(&prefix) {
            return Some(value.trim().to_string());
        }
    }
    None
}

fn unquote(value: String) -> String {
    if value.len() >= 2 && value.starts_with('"') && value.ends_with('"') {
        value[1..value.len() - 1].to_string()
    } else {
        value
    }
}

#[derive(Clone)]
struct FixtureSet {
    ca_cert_der: CertificateDer<'static>,
    ca_key_der: Vec<u8>,
    ca_pem: String,
    ca_key_pem: String,
    server_cert_der: CertificateDer<'static>,
    server_key_der: Vec<u8>,
    server_pem: String,
    server_key_pem: String,
    client_cert_der: CertificateDer<'static>,
    client_key_der: Vec<u8>,
    client_pem: String,
    client_key_pem: String,
}

fn run_server(config: Config) -> Result<(), Box<dyn std::error::Error>> {
    let fixtures = generate_fixture_set()?;
    if let Some(dir) = &config.fixture_dir {
        write_fixtures(dir, &fixtures)?;
        eprintln!("[fixture_dir {}]", dir.display());
    }

    let server_config = build_server_config(&config, &fixtures)?;
    let server_config = Arc::new(server_config);

    let listener = TcpListener::bind(&config.listen)?;
    eprintln!("Listening on {}", config.listen);
    eprintln!(
        "[config accept_count={} require_client_auth={}]",
        config.accept_count, config.require_client_auth
    );

    for connection_idx in 0..config.accept_count {
        let (stream, peer) = listener.accept()?;
        eprintln!(
            "[accept {}/{} from {}]",
            connection_idx + 1,
            config.accept_count,
            peer
        );

        let conn = ServerConnection::new(server_config.clone())?;
        let mut tls = rustls::StreamOwned::new(conn, stream);

        tls.write_all(config.greeting.as_bytes())?;
        tls.write_all(b"\n")?;
        tls.flush()?;

        let mut recv_buf = vec![0u8; 4096];
        let recv_len = tls.read(&mut recv_buf).unwrap_or(0);
        let client_message = if recv_len > 0 {
            String::from_utf8_lossy(&recv_buf[..recv_len]).trim().to_string()
        } else {
            String::new()
        };

        let handshake_kind = match tls.conn.handshake_kind() {
            Some(HandshakeKind::Full) => "full",
            Some(HandshakeKind::FullWithHelloRetryRequest) => "full-hrr",
            Some(HandshakeKind::Resumed) => "resumed",
            None => "unknown",
        };
        let client_cert_count = tls.conn.peer_certificates().map(|v| v.len()).unwrap_or(0);
        let resumed = handshake_kind == "resumed";
        let response = format!(
            "server_ack idx={} resumed={} client_certs={} msg={}\n",
            connection_idx + 1,
            resumed,
            client_cert_count,
            client_message
        );
        tls.write_all(response.as_bytes())?;
        tls.flush()?;

        eprintln!(
            "[accepted idx={} handshake={} client_certs={} msg={}]",
            connection_idx + 1,
            handshake_kind,
            client_cert_count,
            client_message
        );
    }

    println!("[SERVER OK]");
    Ok(())
}

fn generate_fixture_set() -> Result<FixtureSet, Box<dyn std::error::Error>> {
    let ca_key = KeyPair::generate_for(&PKCS_ED25519)?;
    let mut ca_params = CertificateParams::new(vec!["Simple TLS Test CA".to_string()])?;
    ca_params.is_ca = IsCa::Ca(BasicConstraints::Unconstrained);
    ca_params
        .distinguished_name
        .push(DnType::CommonName, "Simple TLS Test CA");
    let ca_cert = ca_params.self_signed(&ca_key)?;
    let ca_cert_der = ca_cert.der().clone();
    let ca_pem = ca_cert.pem();
    let ca_key_der = ca_key.serialize_der();
    let ca_key_pem = ca_key.serialize_pem();

    let (server_cert, server_pem, server_key_der, server_key_pem) =
        issue_leaf_cert(&ca_cert, &ca_key, "localhost", vec!["localhost".to_string()])?;
    let (client_cert, client_pem, client_key_der, client_key_pem) =
        issue_leaf_cert(&ca_cert, &ca_key, "simple-client", vec!["simple-client".to_string()])?;

    Ok(FixtureSet {
        ca_cert_der,
        ca_key_der,
        ca_pem,
        ca_key_pem,
        server_cert_der: server_cert,
        server_key_der,
        server_pem,
        server_key_pem,
        client_cert_der: client_cert,
        client_key_der,
        client_pem,
        client_key_pem,
    })
}

fn issue_leaf_cert(
    issuer: &Certificate,
    issuer_key: &KeyPair,
    common_name: &str,
    sans: Vec<String>,
) -> Result<(CertificateDer<'static>, String, Vec<u8>, String), Box<dyn std::error::Error>> {
    let leaf_key = KeyPair::generate_for(&PKCS_ED25519)?;
    let mut params = CertificateParams::new(sans)?;
    params.distinguished_name.push(DnType::CommonName, common_name);
    let cert: Certificate = params.signed_by(&leaf_key, issuer, issuer_key)?;
    Ok((
        cert.der().clone(),
        cert.pem(),
        leaf_key.serialize_der(),
        leaf_key.serialize_pem(),
    ))
}

fn build_server_config(
    config: &Config,
    fixtures: &FixtureSet,
) -> Result<ServerConfig, Box<dyn std::error::Error>> {
    let provider = Arc::new(rustls::crypto::ring::default_provider());
    let builder = ServerConfig::builder_with_provider(provider)
        .with_protocol_versions(&[&rustls::version::TLS13])?;

    let server_cert_chain = vec![fixtures.server_cert_der.clone()];
    let server_key = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(
        fixtures.server_key_der.clone(),
    ));

    let mut server_config = if config.require_client_auth {
        let mut roots = RootCertStore::empty();
        roots.add(fixtures.ca_cert_der.clone())?;
        let client_verifier = WebPkiClientVerifier::builder(Arc::new(roots)).build()?;
        builder
            .with_client_cert_verifier(client_verifier)
            .with_single_cert(server_cert_chain, server_key)?
    } else {
        builder
            .with_no_client_auth()
            .with_single_cert(server_cert_chain, server_key)?
    };

    server_config.alpn_protocols = vec![b"http/1.1".to_vec(), b"simple-test".to_vec()];
    Ok(server_config)
}

fn write_fixtures(dir: &Path, fixtures: &FixtureSet) -> Result<(), Box<dyn std::error::Error>> {
    fs::create_dir_all(dir)?;
    write_file(dir.join("ca.der"), fixtures.ca_cert_der.as_ref())?;
    write_file(dir.join("ca.key.der"), &fixtures.ca_key_der)?;
    write_text(dir.join("ca.pem"), &fixtures.ca_pem)?;
    write_text(dir.join("ca.key.pem"), &fixtures.ca_key_pem)?;

    write_file(dir.join("server.der"), fixtures.server_cert_der.as_ref())?;
    write_file(dir.join("server.key.der"), &fixtures.server_key_der)?;
    write_text(dir.join("server.pem"), &fixtures.server_pem)?;
    write_text(dir.join("server.key.pem"), &fixtures.server_key_pem)?;

    write_file(dir.join("client.der"), fixtures.client_cert_der.as_ref())?;
    write_file(dir.join("client.key.der"), &fixtures.client_key_der)?;
    write_text(dir.join("client.pem"), &fixtures.client_pem)?;
    write_text(dir.join("client.key.pem"), &fixtures.client_key_pem)?;
    Ok(())
}

fn write_file(path: PathBuf, bytes: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
    fs::write(path, bytes)?;
    Ok(())
}

fn write_text(path: PathBuf, text: &str) -> Result<(), Box<dyn std::error::Error>> {
    fs::write(path, text.as_bytes())?;
    Ok(())
}
