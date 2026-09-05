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

/// Lossless synchronous HTTP contract.
///
/// Simple ABI:
/// `rt_http_request_v2(method, url, headers, body_bytes, timeout_ms)`
/// `-> (status, reason, raw_headers, body_bytes, transport_error)`.
pub fn rt_http_request_v2(args: &[Value]) -> Result<Value, CompileError> {
    use std::io::Read;

    const MAX_RESPONSE_BYTES: u64 = 64 * 1024 * 1024;

    fn result_tuple(status: i64, reason: String, headers: String, body: Vec<u8>, error: String) -> Value {
        Value::Tuple(vec![
            Value::Int(status),
            Value::text(reason),
            Value::text(headers),
            Value::byte_array(body),
            Value::text(error),
        ])
    }

    fn error_tuple(message: impl Into<String>) -> Value {
        result_tuple(-1, String::new(), String::new(), Vec::new(), message.into())
    }

    fn is_http_token(value: &str) -> bool {
        !value.is_empty()
            && value
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || b"!#$%&'*+-.^_`|~".contains(&byte))
    }

    let method = match args.first() {
        Some(Value::Str(value)) if is_http_token(value) => value.as_str(),
        _ => return Ok(error_tuple("rt_http_request_v2: invalid method")),
    };
    let url = match args.get(1) {
        Some(Value::Str(value)) => value.as_str(),
        _ => return Ok(error_tuple("rt_http_request_v2: invalid URL")),
    };
    let body = match args.get(3).and_then(Value::byte_array_view) {
        Some(value) => value,
        None => return Ok(error_tuple("rt_http_request_v2: body must be bytes")),
    };
    let timeout_ms = match args.get(4) {
        Some(Value::Int(value)) if *value >= 0 => *value,
        _ => return Ok(error_tuple("rt_http_request_v2: invalid timeout")),
    };

    static AGENT: std::sync::OnceLock<ureq::Agent> = std::sync::OnceLock::new();
    let agent = AGENT.get_or_init(|| ureq::builder().redirects(0).build());
    let mut request = agent.request(method, url);
    if timeout_ms > 0 {
        request = request.timeout(std::time::Duration::from_millis(timeout_ms as u64));
    }
    if let Some(Value::Array(headers) | Value::FrozenArray(headers)) = args.get(2) {
        if headers.len() > 1024 {
            return Ok(error_tuple("rt_http_request_v2: too many headers"));
        }
        let mut header_bytes = 0usize;
        for header in headers.iter() {
            let Value::Str(header) = header else {
                return Ok(error_tuple("rt_http_request_v2: headers must contain text"));
            };
            let Some(separator) = header.find(':') else {
                return Ok(error_tuple("rt_http_request_v2: malformed header"));
            };
            let name = header[..separator].trim();
            let value = header[separator + 1..].trim();
            header_bytes = match header_bytes.checked_add(header.len()) {
                Some(total) if total <= 1024 * 1024 => total,
                _ => return Ok(error_tuple("rt_http_request_v2: headers exceed 1 MiB")),
            };
            if !is_http_token(name) || value.contains('\r') || value.contains('\n') {
                return Ok(error_tuple("rt_http_request_v2: invalid header"));
            }
            request = request.set(name, value);
        }
    } else {
        return Ok(error_tuple("rt_http_request_v2: headers must be an array"));
    }

    let response = if body.is_empty() {
        request.call()
    } else {
        request.send_bytes(body)
    };
    let response = match response {
        Ok(response) | Err(ureq::Error::Status(_, response)) => response,
        Err(error) => return Ok(error_tuple(format!("rt_http_request_v2 error: {error}"))),
    };
    let status = response.status() as i64;
    let reason = response.status_text().to_string();
    if reason.len() > 8192 {
        return Ok(error_tuple("rt_http_request_v2: status reason exceeds 8 KiB"));
    }
    let mut raw_headers = String::new();
    let response_header_names = response.headers_names();
    if response_header_names.len() > 1024 {
        return Ok(error_tuple("rt_http_request_v2: too many response headers"));
    }
    for name in response_header_names {
        if let Some(value) = response.header(&name) {
            let added = name.len().saturating_add(value.len()).saturating_add(4);
            if raw_headers.len().saturating_add(added) > 1024 * 1024 {
                return Ok(error_tuple("rt_http_request_v2: response headers exceed 1 MiB"));
            }
            raw_headers.push_str(&name);
            raw_headers.push_str(": ");
            raw_headers.push_str(value);
            raw_headers.push_str("\r\n");
        }
    }
    let mut body_bytes = Vec::new();
    let mut reader = response.into_reader().take(MAX_RESPONSE_BYTES + 1);
    if let Err(error) = reader.read_to_end(&mut body_bytes) {
        return Ok(error_tuple(format!("rt_http_request_v2 read error: {error}")));
    }
    if body_bytes.len() as u64 > MAX_RESPONSE_BYTES {
        return Ok(error_tuple("rt_http_request_v2: response exceeds 64 MiB"));
    }
    Ok(result_tuple(status, reason, raw_headers, body_bytes, String::new()))
}

/// Stub for async WebSocket raw read — not available in interpreter mode.
///
/// Returns empty list (List<i64>).
///
/// Callable from Simple as: `rt_async_ws_read_raw(fd: i64, max_size: i64) -> List<i64>`
pub fn rt_async_ws_read_raw(_args: &[Value]) -> Result<Value, CompileError> {
    // WebSocket raw I/O is not supported in interpreter mode; return empty array
    Ok(Value::byte_array(vec![]))
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

#[cfg(test)]
mod http_v2_tests {
    use super::*;

    fn assert_typed_error(value: Value) {
        let Value::Tuple(fields) = value else {
            panic!("expected HTTP v2 tuple")
        };
        assert_eq!(fields.len(), 5);
        assert!(matches!(fields[0], Value::Int(-1)));
        assert!(matches!(&fields[3], value if value.byte_array_view() == Some(&[][..])));
        assert!(matches!(&fields[4], Value::Str(message) if !message.is_empty()));
    }

    #[test]
    fn http_v2_invalid_arguments_fail_as_typed_tuple() {
        assert_typed_error(rt_http_request_v2(&[]).expect("typed failure"));
    }

    #[test]
    fn http_v2_rejects_header_injection_before_io() {
        let args = vec![
            Value::text("GET".to_string()),
            Value::text("http://127.0.0.1/".to_string()),
            Value::array(vec![Value::text("X-Test: ok\r\nInjected: yes".to_string())]),
            Value::byte_array(Vec::new()),
            Value::Int(1),
        ];
        assert_typed_error(rt_http_request_v2(&args).expect("typed failure"));
    }
}
