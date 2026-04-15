// ============================================================================
// TLS transport FFI shims
// ============================================================================
//
// The compiled host runtime does not yet ship a rustls-backed transport layer.
// For current web UI flows TLS is opt-in; the default path is plain HTTP.
// These exports preserve the expected ABI for compiled SMFs by proxying socket
// operations to the existing TCP runtime and returning conservative stub values
// for certificate/configuration helpers.

static NEXT_TLS_FAKE_HANDLE: std::sync::atomic::AtomicI64 = std::sync::atomic::AtomicI64::new(1);

fn next_tls_fake_handle() -> i64 {
    NEXT_TLS_FAKE_HANDLE.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

fn empty_text() -> crate::value::RuntimeValue {
    unsafe { crate::value::collections::rt_string_new(std::ptr::null(), 0) }
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
    _cert_path: crate::value::RuntimeValue,
    _key_path: crate::value::RuntimeValue,
) -> i64 {
    let addr = format!("0.0.0.0:{port}");
    let (handle, err) = unsafe { native_tcp_bind(addr.as_ptr() as i64, addr.len() as i64) };
    if err == NetError::Success as i64 { handle } else { -err }
}

#[no_mangle]
pub extern "C" fn rt_tls_server_accept(server: i64) -> i64 {
    rt_io_tcp_accept(server)
}

#[no_mangle]
pub extern "C" fn rt_tls_server_write(conn: i64, data: crate::value::RuntimeValue) -> i64 {
    write_text_to_stream(conn, data)
}

#[no_mangle]
pub extern "C" fn rt_tls_server_write_bytes(conn: i64, data: crate::value::RuntimeValue) -> i64 {
    write_bytes_to_stream(conn, data)
}

#[no_mangle]
pub extern "C" fn rt_tls_server_read(conn: i64, max_bytes: i64) -> crate::value::RuntimeValue {
    read_text_from_stream(conn, max_bytes)
}

#[no_mangle]
pub extern "C" fn rt_tls_server_close_connection(conn: i64) -> bool {
    native_tcp_close(conn) == NetError::Success as i64
}

#[no_mangle]
pub extern "C" fn rt_tls_server_shutdown(server: i64) -> bool {
    native_tcp_close(server) == NetError::Success as i64
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
