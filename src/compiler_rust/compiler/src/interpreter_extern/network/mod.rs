//! Network operations extern functions
//!
//! Provides TCP, UDP, and HTTP networking operations for Simple language.
//!
//! ## Modules
//! - `tcp`: TCP socket operations (bind, accept, connect, read, write, etc.)
//! - `udp`: UDP socket operations (bind, send, recv, multicast, etc.)
//! - `http`: HTTP client operations
//!
//! All operations delegate to the native network layer (interpreter_native_net)
//! and include proper effect checking for secure execution.

pub mod http;
pub mod tcp;
pub mod udp;

// Re-export all TCP operations
pub use tcp::{
    native_tcp_accept, native_tcp_bind, native_tcp_close, native_tcp_connect, native_tcp_connect_timeout,
    native_tcp_flush, native_tcp_get_nodelay, native_tcp_peek, native_tcp_read, native_tcp_set_backlog,
    native_tcp_set_keepalive, native_tcp_set_nodelay, native_tcp_set_read_timeout, native_tcp_set_write_timeout,
    native_tcp_shutdown, native_tcp_write,
};

// Re-export all UDP operations
pub use udp::{
    native_udp_bind, native_udp_close, native_udp_connect, native_udp_get_broadcast, native_udp_get_ttl,
    native_udp_join_multicast_v4, native_udp_join_multicast_v6, native_udp_leave_multicast_v4,
    native_udp_leave_multicast_v6, native_udp_peer_addr, native_udp_peek, native_udp_peek_from, native_udp_recv,
    native_udp_recv_from, native_udp_send, native_udp_send_to, native_udp_set_broadcast, native_udp_set_multicast_loop,
    native_udp_set_multicast_ttl, native_udp_set_read_timeout, native_udp_set_ttl, native_udp_set_write_timeout,
};

// Re-export HTTP operations
pub use http::native_http_send;

use crate::error::CompileError;
use crate::value::Value;
use std::sync::Arc;

/// Synchronous HTTP GET request using ureq.
///
/// Returns a tuple (status_code: i64, body: text, error: text).
/// On success, error is empty. On failure, status_code is -1 and error has the message.
///
/// Callable from Simple as: `rt_http_get(url: text) -> (i64, text, text)`
pub fn rt_http_get(args: &[Value]) -> Result<Value, CompileError> {
    let url = match args.first() {
        Some(Value::Str(s)) => s.as_ref().clone(),
        _ => {
            return Ok(Value::Tuple(vec![
                Value::Int(-1),
                Value::text(String::new()),
                Value::text("rt_http_get: missing or invalid URL argument".to_string()),
            ]))
        }
    };
    match ureq::get(&url).call() {
        Ok(response) => {
            let status = response.status() as i64;
            let body = response.into_string().unwrap_or_default();
            Ok(Value::Tuple(vec![
                Value::Int(status),
                Value::text(body),
                Value::text(String::new()),
            ]))
        }
        Err(e) => Ok(Value::Tuple(vec![
            Value::Int(-1),
            Value::text(String::new()),
            Value::text(format!("rt_http_get error: {e}")),
        ])),
    }
}

/// Synchronous HTTP request with explicit method, headers, and body using ureq.
///
/// Callable from Simple as:
///   `rt_http_request(method: text, url: text, headers: [text], body: text) -> (i64, text, text)`
/// `headers` is a list of `"Key: Value"` strings. Returns `(status_code, body, error)`.
///
/// HTTP error statuses (4xx/5xx) are returned as a normal `(status, body, "")` tuple so
/// callers can inspect the status and parse the error body (e.g. S3 `NoSuchKey`); only
/// transport/protocol failures set `status = -1` with a non-empty error string.
///
/// Mirrors `rt_http_get` (no `check_effect_violations`, unlike `native_http_send`) so the
/// `rt_http_*` extern family behaves consistently under the bootstrap interpreter.
pub fn rt_http_request(args: &[Value]) -> Result<Value, CompileError> {
    fn err_tuple(msg: String) -> Value {
        Value::Tuple(vec![Value::Int(-1), Value::text(String::new()), Value::text(msg)])
    }
    let method = match args.first() {
        Some(Value::Str(s)) => s.as_ref().clone(),
        _ => {
            return Ok(err_tuple(
                "rt_http_request: missing or invalid method argument".to_string(),
            ))
        }
    };
    let url = match args.get(1) {
        Some(Value::Str(s)) => s.as_ref().clone(),
        _ => {
            return Ok(err_tuple(
                "rt_http_request: missing or invalid url argument".to_string(),
            ))
        }
    };
    // headers: [text] of "Key: Value" (first colon splits; SigV4 Authorization values
    // contain '/' and ',' but no colon before the first one, so this is safe).
    let mut header_pairs: Vec<(String, String)> = Vec::new();
    if let Some(Value::Array(items)) = args.get(2) {
        for it in items.iter() {
            if let Value::Str(h) = it {
                if let Some(idx) = h.find(':') {
                    let k = h[..idx].trim().to_string();
                    let v = h[idx + 1..].trim().to_string();
                    if !k.is_empty() {
                        header_pairs.push((k, v));
                    }
                }
            }
        }
    }
    let body = match args.get(3) {
        Some(Value::Str(s)) => s.as_ref().clone(),
        _ => String::new(),
    };

    let mut req = ureq::request(&method, &url);
    for (k, v) in &header_pairs {
        req = req.set(k, v);
    }
    let send_result = if body.is_empty() {
        req.call()
    } else {
        req.send_string(&body)
    };
    match send_result {
        Ok(response) => {
            let status = response.status() as i64;
            let body = response.into_string().unwrap_or_default();
            Ok(Value::Tuple(vec![
                Value::Int(status),
                Value::text(body),
                Value::text(String::new()),
            ]))
        }
        // ureq surfaces non-2xx/3xx as Err(Status); return the real code + body, not -1.
        Err(ureq::Error::Status(code, response)) => {
            let body = response.into_string().unwrap_or_default();
            Ok(Value::Tuple(vec![
                Value::Int(code as i64),
                Value::text(body),
                Value::text(String::new()),
            ]))
        }
        Err(e) => Ok(err_tuple(format!("rt_http_request error: {e}"))),
    }
}

/// Stub for async WebSocket raw read — not available in interpreter mode.
///
/// Returns empty list (List<i64>).
///
/// Callable from Simple as: `rt_async_ws_read_raw(fd: i64, max_size: i64) -> List<i64>`
pub fn rt_async_ws_read_raw(_args: &[Value]) -> Result<Value, CompileError> {
    // WebSocket raw I/O is not supported in interpreter mode; return empty array
    Ok(Value::Array(Arc::new(vec![])))
}

/// Stub for async WebSocket raw write — not available in interpreter mode.
///
/// Returns -1 (bytes written).
///
/// Callable from Simple as: `rt_async_ws_write_raw(fd: i64, data: List<i64>) -> i64`
pub fn rt_async_ws_write_raw(_args: &[Value]) -> Result<Value, CompileError> {
    // WebSocket raw I/O is not supported in interpreter mode
    Ok(Value::Int(-1))
}
