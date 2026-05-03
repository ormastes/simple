// TLS stubs used when runtime-tls is disabled.

fn empty_text() -> crate::value::RuntimeValue {
    unsafe { crate::value::collections::rt_string_new(b"".as_ptr(), 0) }
}

#[no_mangle]
pub extern "C" fn rt_tls_client_connect(_host: crate::value::RuntimeValue, _port: i64) -> i64 { -1 }

#[no_mangle]
pub extern "C" fn rt_tls_client_connect_with_sni(
    _host: crate::value::RuntimeValue,
    _port: i64,
    _server_name: crate::value::RuntimeValue,
) -> i64 {
    -1
}

#[no_mangle]
pub extern "C" fn rt_tls_client_write(_conn: i64, _data: crate::value::RuntimeValue) -> i64 { -1 }

#[no_mangle]
pub extern "C" fn rt_tls_client_read(_conn: i64, _max_bytes: i64) -> crate::value::RuntimeValue { empty_text() }

#[no_mangle]
pub extern "C" fn rt_tls_client_close(_conn: i64) -> bool { false }

#[no_mangle]
pub extern "C" fn rt_tls_server_create(
    _port: i64,
    _cert_path: crate::value::RuntimeValue,
    _key_path: crate::value::RuntimeValue,
) -> i64 {
    -1
}

#[no_mangle]
pub extern "C" fn rt_tls_server_accept(_server: i64) -> i64 { -1 }

#[no_mangle]
pub extern "C" fn rt_tls_server_write(_conn: i64, _data: crate::value::RuntimeValue) -> i64 { -1 }

#[no_mangle]
pub extern "C" fn rt_tls_server_write_bytes(_conn: i64, _data: crate::value::RuntimeValue) -> i64 { -1 }

#[no_mangle]
pub extern "C" fn rt_tls_server_read(_conn: i64, _max_bytes: i64) -> crate::value::RuntimeValue { empty_text() }

#[no_mangle]
pub extern "C" fn rt_tls_server_close_connection(_conn: i64) -> bool { false }

#[no_mangle]
pub extern "C" fn rt_tls_server_shutdown(_server: i64) -> bool { false }

#[no_mangle]
pub extern "C" fn rt_tls_load_cert(_cert_path: crate::value::RuntimeValue) -> i64 { -1 }

#[no_mangle]
pub extern "C" fn rt_tls_load_key(_key_path: crate::value::RuntimeValue) -> i64 { -1 }

#[no_mangle]
pub extern "C" fn rt_tls_verify_cert(_cert: i64) -> bool { false }

#[no_mangle]
pub extern "C" fn rt_tls_get_cert_subject(_cert: i64) -> crate::value::RuntimeValue { empty_text() }

#[no_mangle]
pub extern "C" fn rt_tls_get_cert_issuer(_cert: i64) -> crate::value::RuntimeValue { empty_text() }

#[no_mangle]
pub extern "C" fn rt_tls_get_cert_expiry(_cert: i64) -> crate::value::RuntimeValue { empty_text() }

#[no_mangle]
pub extern "C" fn rt_tls_free_cert(_cert: i64) -> bool { false }

#[no_mangle]
pub extern "C" fn rt_tls_client_config_new() -> i64 { -1 }

#[no_mangle]
pub extern "C" fn rt_tls_client_config_add_root_cert(
    _config: i64,
    _cert_path: crate::value::RuntimeValue,
) -> bool {
    false
}

#[no_mangle]
pub extern "C" fn rt_tls_client_config_set_alpn(
    _config: i64,
    _protocols: crate::value::RuntimeValue,
) -> bool {
    false
}

#[no_mangle]
pub extern "C" fn rt_tls_client_config_enable_sni(_config: i64, _enabled: bool) -> bool { false }

#[no_mangle]
pub extern "C" fn rt_tls_client_config_set_verify_mode(_config: i64, _verify: bool) -> bool { false }

#[no_mangle]
pub extern "C" fn rt_tls_client_config_free(_config: i64) -> bool { false }

#[no_mangle]
pub extern "C" fn rt_tls_server_config_new(
    _cert_path: crate::value::RuntimeValue,
    _key_path: crate::value::RuntimeValue,
) -> i64 {
    -1
}

#[no_mangle]
pub extern "C" fn rt_tls_server_config_set_alpn(
    _config: i64,
    _protocols: crate::value::RuntimeValue,
) -> bool {
    false
}

#[no_mangle]
pub extern "C" fn rt_tls_server_config_require_client_cert(_config: i64, _require: bool) -> bool { false }

#[no_mangle]
pub extern "C" fn rt_tls_server_config_free(_config: i64) -> bool { false }

#[no_mangle]
pub extern "C" fn rt_tls_get_peer_cert(_conn: i64) -> i64 { -1 }

#[no_mangle]
pub extern "C" fn rt_tls_get_protocol_version(_conn: i64) -> crate::value::RuntimeValue { empty_text() }

#[no_mangle]
pub extern "C" fn rt_tls_get_cipher_suite(_conn: i64) -> crate::value::RuntimeValue { empty_text() }

#[no_mangle]
pub extern "C" fn rt_tls_get_negotiated_alpn(_conn: i64) -> crate::value::RuntimeValue { empty_text() }

#[no_mangle]
pub extern "C" fn rt_tls_is_handshake_complete(_conn: i64) -> bool { false }

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
