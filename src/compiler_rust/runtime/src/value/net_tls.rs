// ============================================================================
// TLS transport FFI shims — rustls-backed server, TCP-shim client
// ============================================================================
//
// Server path: `rt_tls_server_create/accept/read/write/close/shutdown` run real
// TLS via rustls 0.23 (ring crypto provider; aws-lc-rs is not vendored).
// Listeners own a `std::net::TcpListener` + an `Arc<rustls::ServerConfig>`;
// per-connection state is a `(ServerConnection, TcpStream)` pair protected by
// a fine-grained mutex so the per-connection thread_spawn2 pattern in
// `src/app/ui.web/tls_serve_loop.spl` can serve multiple TLS clients in
// parallel.  Handles live in a separate table from the TCP-native handles;
// `is_valid_handle(h)` only checks `h != 0` so the two namespaces coexist.
//
// Client path: still a thin shim over plain TCP — v3 roadmap.

static NEXT_TLS_FAKE_HANDLE: std::sync::atomic::AtomicI64 = std::sync::atomic::AtomicI64::new(1);

fn next_tls_fake_handle() -> i64 {
    NEXT_TLS_FAKE_HANDLE.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

fn empty_text() -> crate::value::RuntimeValue {
    unsafe { crate::value::collections::rt_string_new(std::ptr::null(), 0) }
}

// ---------------------------------------------------------------------------
// rustls handle tables (server side)
// ---------------------------------------------------------------------------

struct TlsListenerEntry {
    listener: std::net::TcpListener,
    config: std::sync::Arc<rustls::ServerConfig>,
}

struct TlsConnEntry {
    conn: rustls::ServerConnection,
    stream: std::net::TcpStream,
}

lazy_static::lazy_static! {
    static ref TLS_LISTENERS: std::sync::Mutex<HashMap<i64, std::sync::Arc<std::sync::Mutex<TlsListenerEntry>>>> =
        std::sync::Mutex::new(HashMap::new());
    static ref TLS_CONNS: std::sync::Mutex<HashMap<i64, std::sync::Arc<std::sync::Mutex<TlsConnEntry>>>> =
        std::sync::Mutex::new(HashMap::new());
}

const TLS_HANDLE_BIT: i64 = 0x4000_0000_0000_0000;

static NEXT_RUSTLS_HANDLE: std::sync::atomic::AtomicI64 = std::sync::atomic::AtomicI64::new(1);

fn next_rustls_listener_handle() -> i64 {
    TLS_HANDLE_BIT | (NEXT_RUSTLS_HANDLE.fetch_add(1, std::sync::atomic::Ordering::SeqCst) << 1)
}

fn next_rustls_conn_handle() -> i64 {
    TLS_HANDLE_BIT | (NEXT_RUSTLS_HANDLE.fetch_add(1, std::sync::atomic::Ordering::SeqCst) << 1) | 1
}

fn runtime_value_to_path_string(v: crate::value::RuntimeValue) -> Option<String> {
    let (ptr, len) = runtime_text_ptr_len(v)?;
    if ptr == 0 || len <= 0 {
        return Some(String::new());
    }
    let slice = unsafe { std::slice::from_raw_parts(ptr as *const u8, len as usize) };
    std::str::from_utf8(slice).ok().map(|s| s.to_string())
}

fn parse_pem_blocks(data: &str) -> Vec<(String, Vec<u8>)> {
    use base64::Engine;
    let engine = base64::engine::general_purpose::STANDARD;
    let mut blocks = Vec::new();
    let mut it = data.lines();
    while let Some(line) = it.next() {
        let trimmed = line.trim();
        let label = match trimmed.strip_prefix("-----BEGIN ").and_then(|s| s.strip_suffix("-----")) {
            Some(l) => l.to_string(),
            None => continue,
        };
        let mut b64 = String::new();
        for inner in it.by_ref() {
            let inner_trim = inner.trim();
            if inner_trim.starts_with("-----END ") { break; }
            b64.push_str(inner_trim);
        }
        if let Ok(bytes) = engine.decode(&b64) {
            blocks.push((label, bytes));
        }
    }
    blocks
}

fn load_tls_certs(path: &std::path::Path) -> Result<Vec<rustls::pki_types::CertificateDer<'static>>, String> {
    let data = std::fs::read_to_string(path).map_err(|e| format!("cert open {:?}: {}", path, e))?;
    let mut out = Vec::new();
    for (label, bytes) in parse_pem_blocks(&data) {
        if label == "CERTIFICATE" {
            out.push(rustls::pki_types::CertificateDer::from(bytes));
        }
    }
    if out.is_empty() {
        return Err("no CERTIFICATE blocks found in PEM".into());
    }
    Ok(out)
}

fn load_tls_key(path: &std::path::Path) -> Result<rustls::pki_types::PrivateKeyDer<'static>, String> {
    let data = std::fs::read_to_string(path).map_err(|e| format!("key open {:?}: {}", path, e))?;
    for (label, bytes) in parse_pem_blocks(&data) {
        match label.as_str() {
            "PRIVATE KEY" => return Ok(rustls::pki_types::PrivateKeyDer::Pkcs8(bytes.into())),
            "RSA PRIVATE KEY" => return Ok(rustls::pki_types::PrivateKeyDer::Pkcs1(bytes.into())),
            "EC PRIVATE KEY" => return Ok(rustls::pki_types::PrivateKeyDer::Sec1(bytes.into())),
            _ => continue,
        }
    }
    Err("no PRIVATE KEY / RSA PRIVATE KEY / EC PRIVATE KEY block found".into())
}

fn read_text_from_stream(handle: i64, max_bytes: i64) -> crate::value::RuntimeValue {
    if max_bytes <= 0 {
        return empty_text();
    }
    let size = max_bytes.min(65_536);
    let mut buffer = vec![0u8; size as usize];
    let (read, err) = unsafe { native_tcp_read(handle, buffer.as_mut_ptr() as i64, size) };
    if err != NetError::Success as i64 || read <= 0 {
        return empty_text();
    }
    unsafe { crate::value::collections::rt_string_new(buffer.as_ptr(), read as u64) }
}

fn write_text_to_stream(handle: i64, data: crate::value::RuntimeValue) -> i64 {
    let Some((ptr, len)) = runtime_text_ptr_len(data) else {
        return -1;
    };
    let (written, err) = unsafe { native_tcp_write(handle, ptr, len) };
    if err == NetError::Success as i64 { written } else { -err }
}

fn write_bytes_to_stream(handle: i64, data: crate::value::RuntimeValue) -> i64 {
    let Some(bytes) = runtime_byte_array_to_vec(data) else {
        return -1;
    };
    let (written, err) = unsafe { native_tcp_write(handle, bytes.as_ptr() as i64, bytes.len() as i64) };
    if err == NetError::Success as i64 { written } else { -err }
}

#[no_mangle]
pub extern "C" fn rt_tls_client_connect(host: crate::value::RuntimeValue, port: i64) -> i64 {
    let Some((ptr, len)) = runtime_text_ptr_len(host) else {
        return -(NetError::InvalidAddress as i64);
    };
    let host_str = unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(ptr as *const u8, len as usize)) };
    let addr = format!("{host_str}:{port}");
    let (handle, _local_addr, err) = unsafe { native_tcp_connect(addr.as_ptr() as i64, addr.len() as i64) };
    if err == NetError::Success as i64 { handle } else { -err }
}

#[no_mangle]
pub extern "C" fn rt_tls_client_connect_with_sni(
    host: crate::value::RuntimeValue,
    port: i64,
    _server_name: crate::value::RuntimeValue,
) -> i64 {
    rt_tls_client_connect(host, port)
}

#[no_mangle]
pub extern "C" fn rt_tls_client_write(conn: i64, data: crate::value::RuntimeValue) -> i64 {
    write_text_to_stream(conn, data)
}

#[no_mangle]
pub extern "C" fn rt_tls_client_read(conn: i64, max_bytes: i64) -> crate::value::RuntimeValue {
    read_text_from_stream(conn, max_bytes)
}

#[no_mangle]
pub extern "C" fn rt_tls_client_close(conn: i64) -> bool {
    native_tcp_close(conn) == NetError::Success as i64
}

#[no_mangle]
pub extern "C" fn rt_tls_server_create(
    port: i64,
    cert_path: crate::value::RuntimeValue,
    key_path: crate::value::RuntimeValue,
) -> i64 {
    let Some(cert_path_str) = runtime_value_to_path_string(cert_path) else { return -1; };
    let Some(key_path_str) = runtime_value_to_path_string(key_path) else { return -1; };
    if cert_path_str.is_empty() || key_path_str.is_empty() {
        eprintln!("rt_tls_server_create: cert_path or key_path is empty");
        return -1;
    }
    let certs = match load_tls_certs(std::path::Path::new(&cert_path_str)) {
        Ok(c) => c,
        Err(e) => { eprintln!("rt_tls_server_create: {}", e); return -1; }
    };
    let key = match load_tls_key(std::path::Path::new(&key_path_str)) {
        Ok(k) => k,
        Err(e) => { eprintln!("rt_tls_server_create: {}", e); return -1; }
    };
    let provider = std::sync::Arc::new(rustls::crypto::ring::default_provider());
    let config = match rustls::ServerConfig::builder_with_provider(provider)
        .with_safe_default_protocol_versions()
        .and_then(|b| b.with_no_client_auth().with_single_cert(certs, key)
            .map_err(|e| rustls::Error::General(format!("{}", e))))
    {
        Ok(c) => c,
        Err(e) => { eprintln!("rt_tls_server_create: build config: {}", e); return -1; }
    };
    let addr = format!("0.0.0.0:{}", port);
    let listener = match std::net::TcpListener::bind(&addr) {
        Ok(l) => l,
        Err(e) => { eprintln!("rt_tls_server_create: bind {}: {}", addr, e); return -1; }
    };
    let handle = next_rustls_listener_handle();
    TLS_LISTENERS.lock().unwrap().insert(
        handle,
        std::sync::Arc::new(std::sync::Mutex::new(TlsListenerEntry {
            listener,
            config: std::sync::Arc::new(config),
        })),
    );
    handle
}

#[no_mangle]
pub extern "C" fn rt_tls_server_accept(server: i64) -> i64 {
    let entry_arc = {
        let guard = TLS_LISTENERS.lock().unwrap();
        match guard.get(&server) { Some(a) => a.clone(), None => return -1 }
    };
    let (stream, config) = {
        let entry = entry_arc.lock().unwrap();
        let accept_result = entry.listener.accept();
        let config = entry.config.clone();
        drop(entry);
        match accept_result { Ok((s, _)) => (s, config), Err(_) => return -1 }
    };
    let conn = match rustls::ServerConnection::new(config) {
        Ok(c) => c,
        Err(_) => return -1,
    };
    let handle = next_rustls_conn_handle();
    TLS_CONNS.lock().unwrap().insert(
        handle,
        std::sync::Arc::new(std::sync::Mutex::new(TlsConnEntry { conn, stream })),
    );
    handle
}

#[no_mangle]
pub extern "C" fn rt_tls_server_write(conn: i64, data: crate::value::RuntimeValue) -> i64 {
    let Some((ptr, len)) = runtime_text_ptr_len(data) else { return -1; };
    if ptr == 0 || len < 0 { return -1; }
    let slice = unsafe { std::slice::from_raw_parts(ptr as *const u8, len as usize) };
    tls_server_write_bytes_impl(conn, slice)
}

#[no_mangle]
pub extern "C" fn rt_tls_server_write_bytes(conn: i64, data: crate::value::RuntimeValue) -> i64 {
    let Some(bytes) = runtime_byte_array_to_vec(data) else { return -1; };
    tls_server_write_bytes_impl(conn, &bytes)
}

fn tls_server_write_bytes_impl(conn: i64, bytes: &[u8]) -> i64 {
    let entry_arc = {
        let guard = TLS_CONNS.lock().unwrap();
        match guard.get(&conn) { Some(a) => a.clone(), None => return -1 }
    };
    let mut entry_guard = entry_arc.lock().unwrap();
    let entry = &mut *entry_guard;
    let mut tls_stream = rustls::Stream::new(&mut entry.conn, &mut entry.stream);
    match tls_stream.write_all(bytes) {
        Ok(()) => bytes.len() as i64,
        Err(_) => -1,
    }
}

#[no_mangle]
pub extern "C" fn rt_tls_server_read(conn: i64, max_bytes: i64) -> crate::value::RuntimeValue {
    if max_bytes <= 0 { return empty_text(); }
    let entry_arc = {
        let guard = TLS_CONNS.lock().unwrap();
        match guard.get(&conn) { Some(a) => a.clone(), None => return empty_text() }
    };
    let size = max_bytes.min(65_536) as usize;
    let mut buf = vec![0u8; size];
    let n = {
        let mut entry_guard = entry_arc.lock().unwrap();
        let entry = &mut *entry_guard;
        let mut tls_stream = rustls::Stream::new(&mut entry.conn, &mut entry.stream);
        match tls_stream.read(&mut buf) { Ok(n) => n, Err(_) => return empty_text() }
    };
    if n == 0 { return empty_text(); }
    unsafe { crate::value::collections::rt_string_new(buf.as_ptr(), n as u64) }
}

#[no_mangle]
pub extern "C" fn rt_tls_server_close_connection(conn: i64) -> bool {
    let removed = TLS_CONNS.lock().unwrap().remove(&conn);
    if let Some(arc) = removed {
        let mut entry = arc.lock().unwrap();
        entry.conn.send_close_notify();
        let _ = entry.stream.shutdown(std::net::Shutdown::Both);
        true
    } else { false }
}

#[no_mangle]
pub extern "C" fn rt_tls_server_shutdown(server: i64) -> bool {
    TLS_LISTENERS.lock().unwrap().remove(&server).is_some()
}

#[no_mangle]
pub extern "C" fn rt_tls_load_cert(_cert_path: crate::value::RuntimeValue) -> i64 {
    next_tls_fake_handle()
}

#[no_mangle]
pub extern "C" fn rt_tls_load_key(_key_path: crate::value::RuntimeValue) -> i64 {
    next_tls_fake_handle()
}

#[no_mangle]
pub extern "C" fn rt_tls_verify_cert(_cert: i64) -> bool {
    false
}

#[no_mangle]
pub extern "C" fn rt_tls_get_cert_subject(_cert: i64) -> crate::value::RuntimeValue {
    empty_text()
}

#[no_mangle]
pub extern "C" fn rt_tls_get_cert_issuer(_cert: i64) -> crate::value::RuntimeValue {
    empty_text()
}

#[no_mangle]
pub extern "C" fn rt_tls_get_cert_expiry(_cert: i64) -> crate::value::RuntimeValue {
    empty_text()
}

#[no_mangle]
pub extern "C" fn rt_tls_free_cert(_cert: i64) -> bool {
    true
}

#[no_mangle]
pub extern "C" fn rt_tls_client_config_new() -> i64 {
    next_tls_fake_handle()
}

#[no_mangle]
pub extern "C" fn rt_tls_client_config_add_root_cert(
    _config: i64,
    _cert_path: crate::value::RuntimeValue,
) -> bool {
    true
}

#[no_mangle]
pub extern "C" fn rt_tls_client_config_set_alpn(
    _config: i64,
    _protocols: crate::value::RuntimeValue,
) -> bool {
    true
}

#[no_mangle]
pub extern "C" fn rt_tls_client_config_enable_sni(_config: i64, _enabled: bool) -> bool {
    true
}

#[no_mangle]
pub extern "C" fn rt_tls_client_config_set_verify_mode(_config: i64, _verify: bool) -> bool {
    true
}

#[no_mangle]
pub extern "C" fn rt_tls_client_config_free(_config: i64) -> bool {
    true
}

#[no_mangle]
pub extern "C" fn rt_tls_server_config_new(
    _cert_path: crate::value::RuntimeValue,
    _key_path: crate::value::RuntimeValue,
) -> i64 {
    next_tls_fake_handle()
}

#[no_mangle]
pub extern "C" fn rt_tls_server_config_set_alpn(
    _config: i64,
    _protocols: crate::value::RuntimeValue,
) -> bool {
    true
}

#[no_mangle]
pub extern "C" fn rt_tls_server_config_require_client_cert(_config: i64, _require: bool) -> bool {
    true
}

#[no_mangle]
pub extern "C" fn rt_tls_server_config_free(_config: i64) -> bool {
    true
}

#[no_mangle]
pub extern "C" fn rt_tls_get_peer_cert(_conn: i64) -> i64 {
    next_tls_fake_handle()
}

#[no_mangle]
pub extern "C" fn rt_tls_get_protocol_version(_conn: i64) -> crate::value::RuntimeValue {
    unsafe { crate::value::collections::rt_string_new(b"tcp".as_ptr(), 3) }
}

#[no_mangle]
pub extern "C" fn rt_tls_get_cipher_suite(_conn: i64) -> crate::value::RuntimeValue {
    empty_text()
}

#[no_mangle]
pub extern "C" fn rt_tls_get_negotiated_alpn(_conn: i64) -> crate::value::RuntimeValue {
    empty_text()
}

#[no_mangle]
pub extern "C" fn rt_tls_is_handshake_complete(_conn: i64) -> bool {
    true
}

#[no_mangle]
pub extern "C" fn rt_tls_generate_self_signed_cert(
    _common_name: crate::value::RuntimeValue,
    _days_valid: i64,
    _cert_out: crate::value::RuntimeValue,
    _key_out: crate::value::RuntimeValue,
) -> bool {
    false
}

#[no_mangle]
pub extern "C" fn rt_tls_hash_cert(_cert_path: crate::value::RuntimeValue) -> crate::value::RuntimeValue {
    empty_text()
}
