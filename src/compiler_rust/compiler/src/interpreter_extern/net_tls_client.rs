//! Interpreter-mode `rt_tls_client_*` — delegates to the runtime's rustls
//! implementation instead of stubbing.
//!
//! Until 2026-08-16 these nine externs were registered to stubs that
//! unconditionally returned `-1` / empty text / `false`
//! ("TLS client stubs (interpreter mode — no real TLS)"), so every
//! `https://` fetch under `bin/simple run` failed its handshake with
//! `h1: missing TLS connection` regardless of network reachability, while
//! plain TCP (`interpreter_native_net.rs`) was real. The runtime crate has
//! had a real rustls 0.23 client the whole time (`value/net_tls.rs`,
//! feature `runtime-tls`); the seed simply never called it.
//!
//! These delegates are honest under EITHER feature state: the runtime
//! exports the same `rt_tls_client_*` symbols from `net_tls.rs` (real) and
//! `net_tls_stub.rs` (refusing), so when a build lacks `runtime-tls` the
//! behaviour degrades to exactly the old refusal — never a fake success.
//! The seed driver crate now enables `runtime-tls` so `bin/simple run` gets
//! the real client.
//!
//! Marshaling follows `cranelift.rs`: `Value::Str` -> `rt_string_new`
//! (runtime-owned, deliberately not freed here — same single-leak-per-call
//! contract every other RuntimeValue bridge in this directory uses), and
//! returned runtime strings are copied out via `rt_string_len`/`rt_string_data`.

use crate::error::CompileError;
use crate::value::Value;
use simple_runtime::RuntimeValue;
use simple_runtime::value::net;

fn text_arg(args: &[Value], index: usize) -> RuntimeValue {
    match args.get(index) {
        Some(Value::Str(s)) => {
            simple_runtime::value::rt_string_new(s.as_ptr(), s.len() as u64)
        }
        _ => RuntimeValue::NIL,
    }
}

fn int_arg(args: &[Value], index: usize) -> i64 {
    match args.get(index) {
        Some(Value::Int(i)) => *i,
        _ => 0,
    }
}

fn runtime_text_out(rv: RuntimeValue, symbol: &str) -> Result<Value, CompileError> {
    let len = simple_runtime::value::rt_string_len(rv);
    let data = if len <= 0 {
        std::ptr::null()
    } else {
        simple_runtime::value::rt_string_data(rv)
    };
    unsafe { text_from_runtime_parts(data, len, symbol) }
}

unsafe fn text_from_runtime_parts(data: *const u8, len: i64, symbol: &str) -> Result<Value, CompileError> {
    if len <= 0 {
        return Ok(Value::text(String::new()));
    }
    if data.is_null() {
        return Err(CompileError::runtime(format!(
            "{symbol}: foreign text contract returned null with length {len}"
        )));
    }
    unsafe {
        let slice = std::slice::from_raw_parts(data, len as usize);
        Ok(Value::text(String::from_utf8_lossy(slice).to_string()))
    }
}

/// `rt_tls_client_connect(host, port) -> i64`
pub fn rt_tls_client_connect(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(net::rt_tls_client_connect(
        text_arg(args, 0),
        int_arg(args, 1),
    )))
}

/// `rt_tls_client_connect_with_sni(host, port, server_name) -> i64`
pub fn rt_tls_client_connect_with_sni(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(net::rt_tls_client_connect_with_sni(
        text_arg(args, 0),
        int_arg(args, 1),
        text_arg(args, 2),
    )))
}

/// `rt_tls_client_connect_address_with_sni_timeout(address, port, server_name, timeout_ms) -> i64`
pub fn rt_tls_client_connect_address_with_sni_timeout(
    args: &[Value],
) -> Result<Value, CompileError> {
    Ok(Value::Int(net::rt_tls_client_connect_address_with_sni_timeout(
        text_arg(args, 0),
        int_arg(args, 1),
        text_arg(args, 2),
        int_arg(args, 3),
    )))
}

/// `rt_tls_client_write(conn, data) -> i64`
pub fn rt_tls_client_write(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(net::rt_tls_client_write(
        int_arg(args, 0),
        text_arg(args, 1),
    )))
}

/// `rt_tls_client_write_timeout(conn, data, timeout_ms) -> i64`
pub fn rt_tls_client_write_timeout(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(net::rt_tls_client_write_timeout(
        int_arg(args, 0),
        text_arg(args, 1),
        int_arg(args, 2),
    )))
}

/// `rt_tls_client_read(conn, max_bytes) -> text`
pub fn rt_tls_client_read(args: &[Value]) -> Result<Value, CompileError> {
    runtime_text_out(
        net::rt_tls_client_read(int_arg(args, 0), int_arg(args, 1)),
        "rt_tls_client_read",
    )
}

/// `rt_tls_client_read_timeout(conn, max_bytes, timeout_ms) -> text`
pub fn rt_tls_client_read_timeout(args: &[Value]) -> Result<Value, CompileError> {
    runtime_text_out(
        net::rt_tls_client_read_timeout(int_arg(args, 0), int_arg(args, 1), int_arg(args, 2)),
        "rt_tls_client_read_timeout",
    )
}

/// `rt_tls_client_close(conn) -> bool`
pub fn rt_tls_client_close(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(net::rt_tls_client_close(int_arg(args, 0))))
}

/// `rt_tls_get_protocol_version(conn) -> text`
pub fn rt_tls_get_protocol_version(args: &[Value]) -> Result<Value, CompileError> {
    runtime_text_out(
        net::rt_tls_get_protocol_version(int_arg(args, 0)),
        "rt_tls_get_protocol_version",
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn null_positive_length_text_is_a_contract_error() {
        let result = unsafe { text_from_runtime_parts(std::ptr::null(), 1, "rt_tls_client_read") };
        assert!(result.is_err(), "null foreign text must never become empty text");
    }

    #[test]
    fn zero_length_text_remains_valid_empty_text() {
        let result = unsafe { text_from_runtime_parts(std::ptr::null(), 0, "rt_tls_client_read") };
        assert!(result.is_ok(), "zero-length text may use a null data pointer");
    }
}
