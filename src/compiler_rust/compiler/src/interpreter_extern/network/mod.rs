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
    // `body: [u8]` arrives packed (`ByteArray`) or, for a pure-Simple `[u8]`
    // literal, as boxed `Int`/`UInt` elements; both are bytes. Anything outside
    // 0..=255 still fails closed before I/O.
    let body = match args.get(3).and_then(Value::try_array_bytes) {
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
    let mut sent_headers: Vec<(String, String)> = Vec::new();
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
            // ureq's `set` (header::add_header): replace an exactly-named
            // earlier header, except `x-*`/`X-*` headers, which accumulate.
            if !name.starts_with("x-") && !name.starts_with("X-") {
                sent_headers.retain(|(sent, _)| sent != name);
            }
            sent_headers.push((name.to_string(), value.to_string()));
        }
    } else {
        return Ok(error_tuple("rt_http_request_v2: headers must be an array"));
    }

    // ureq parses the URL with the WHATWG `url` crate, which removes `.`/`..`
    // segments (plain or %2e-encoded). A caller that signed the raw path (S3
    // SigV4) needs it on the wire byte-exact, as the C runtime sends it.
    if let Some(target) = verbatim_request_target(url).filter(|target| has_dot_segment(target)) {
        let request_url = match request.request_url() {
            Ok(value) => value,
            Err(error) => return Ok(error_tuple(format!("rt_http_request_v2 error: {error}"))),
        };
        if request_url.scheme() != "http" {
            return Ok(error_tuple(
                "rt_http_request_v2: dot-segment path cannot be sent verbatim over https",
            ));
        }
        // The url crate silently drops tab/CR/LF; the raw target must not carry
        // them (request splitting) or any other control/space byte, as in the
        // C twin's "invalid HTTP URL" check.
        if target.bytes().any(|byte| byte <= 0x20 || byte == 0x7f) {
            return Ok(error_tuple("rt_http_request_v2: invalid URL"));
        }
        // ureq would chunk-encode for a caller Transfer-Encoding and add Basic
        // auth from URL userinfo; this lane does neither, so refuse rather than
        // send different framing or credentials. `Connection: close` is how
        // this lane ends a response without length, so the caller cannot
        // override it.
        if !request_url.as_url().username().is_empty() || request_url.as_url().password().is_some() {
            return Ok(error_tuple(
                "rt_http_request_v2: URL credentials are not supported with a dot-segment path",
            ));
        }
        if sent_headers.iter().any(|(name, _)| {
            name.eq_ignore_ascii_case("transfer-encoding") || name.eq_ignore_ascii_case("connection")
        }) {
            return Ok(error_tuple(
                "rt_http_request_v2: Transfer-Encoding/Connection headers are not supported with a dot-segment path",
            ));
        }
        return Ok(
            match verbatim_http_exchange(
                method,
                &request_url,
                &target,
                &sent_headers,
                &body,
                timeout_ms,
                MAX_RESPONSE_BYTES as usize,
            ) {
                Ok((status, reason, headers, body)) => result_tuple(status, reason, headers, body, String::new()),
                Err(message) => error_tuple(message),
            },
        );
    }

    let response = if body.is_empty() {
        request.call()
    } else {
        request.send_bytes(&body)
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

/// The request target exactly as the caller wrote it: everything after the
/// authority, with the fragment dropped (never sent) and `/` for an empty path.
/// `None` when the URL has no `scheme://` prefix (ureq reports that error).
fn verbatim_request_target(url: &str) -> Option<String> {
    let authority = &url[url.find("://")? + 3..];
    // http/https treat `\\` like `/`, so it also ends the authority.
    let target = &authority[authority.find(['/', '\\', '?', '#']).unwrap_or(authority.len())..];
    let target = &target[..target.find('#').unwrap_or(target.len())];
    Some(match target.as_bytes().first() {
        None => "/".to_string(),
        Some(b'?') => format!("/{target}"),
        Some(_) => target.to_string(),
    })
}

/// True when the path part of `target` has a `.` or `..` segment, plain or
/// `%2e`-encoded: exactly the segments the WHATWG URL parser inside ureq
/// removes (it also treats `\` as a separator for http/https and ignores
/// tab/CR/LF).
fn has_dot_segment(target: &str) -> bool {
    let path = &target[..target.find('?').unwrap_or(target.len())];
    path.split(['/', '\\']).any(|segment| {
        // The URL parser drops tab/CR/LF before it looks at segments.
        let segment = segment.replace(['\t', '\r', '\n'], "").to_ascii_lowercase().replace("%2e", ".");
        segment == "." || segment == ".."
    })
}

fn find_bytes(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    haystack.windows(needle.len()).position(|window| window == needle)
}

/// Decode a complete chunked body; `Ok(None)` while more bytes are needed.
fn decode_chunked(data: &[u8], max_body: usize) -> Result<Option<Vec<u8>>, String> {
    let mut out = Vec::new();
    let mut pos = 0;
    loop {
        let Some(line_end) = find_bytes(&data[pos..], b"\r\n") else {
            return Ok(None);
        };
        let line = std::str::from_utf8(&data[pos..pos + line_end])
            .map_err(|_| "rt_http_request_v2: invalid chunk size".to_string())?;
        let size_text = line.split(';').next().unwrap_or("").trim();
        if size_text.is_empty() || !size_text.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err("rt_http_request_v2: invalid chunk size".to_string());
        }
        let size = usize::from_str_radix(size_text, 16)
            .map_err(|_| "rt_http_request_v2: invalid chunk size".to_string())?;
        pos += line_end + 2;
        if size == 0 {
            // Trailer fields, terminated by an empty line.
            loop {
                let Some(end) = find_bytes(&data[pos..], b"\r\n") else {
                    return Ok(None);
                };
                pos += end + 2;
                if end == 0 {
                    return Ok(Some(out));
                }
            }
        }
        if size > max_body - out.len() {
            return Err("rt_http_request_v2: response exceeds 64 MiB".to_string());
        }
        if data.len() < pos + size + 2 {
            return Ok(None);
        }
        out.extend_from_slice(&data[pos..pos + size]);
        if &data[pos + size..pos + size + 2] != b"\r\n" {
            return Err("rt_http_request_v2: invalid chunk terminator".to_string());
        }
        pos += size + 2;
    }
}

/// HTTP/1.1 exchange over a plain socket that writes `target` byte-exact in
/// the request line, mirroring the C runtime's POSIX `rt_http_perform` (Host,
/// caller headers, Content-Length, `Connection: close`). Used only for http://
/// targets with dot segments, which ureq would otherwise normalise away.
/// Returns `(status, reason, raw_headers, body)` with the ureq lane's shape and
/// limits: lowercased header names, 1024 headers / 1 MiB, 8 KiB reason.
fn verbatim_http_exchange(
    method: &str,
    url: &ureq::RequestUrl,
    target: &str,
    headers: &[(String, String)],
    body: &[u8],
    timeout_ms: i64,
    max_body: usize,
) -> Result<(i64, String, String, Vec<u8>), String> {
    use std::io::{Read, Write};
    use std::net::ToSocketAddrs;
    use std::time::{Duration, Instant};

    let deadline = (timeout_ms > 0).then(|| Instant::now() + Duration::from_millis(timeout_ms as u64));
    let remaining = || -> Result<Option<Duration>, String> {
        match deadline {
            None => Ok(None),
            Some(deadline) => match deadline.checked_duration_since(Instant::now()) {
                Some(left) if !left.is_zero() => Ok(Some(left)),
                _ => Err("rt_http_request_v2 error: timed out".to_string()),
            },
        }
    };
    let io_error = |error: std::io::Error| format!("rt_http_request_v2 error: {error}");

    let host = url.host();
    let port = url.port().unwrap_or(80);
    let connect_host = host.trim_start_matches('[').trim_end_matches(']');
    let addrs = (connect_host, port)
        .to_socket_addrs()
        .map_err(|error| format!("rt_http_request_v2 error: {host}: {error}"))?;
    let mut stream = None;
    let mut last_error = None;
    for addr in addrs {
        // ureq's default connect timeout is 30 s when no overall timeout is set.
        let connect_budget = remaining()?.unwrap_or(Duration::from_secs(30));
        let attempt = std::net::TcpStream::connect_timeout(&addr, connect_budget);
        match attempt {
            Ok(connected) => {
                stream = Some(connected);
                break;
            }
            Err(error) => last_error = Some(error),
        }
    }
    let Some(mut stream) = stream else {
        return Err(match last_error {
            Some(error) => io_error(error),
            None => format!("rt_http_request_v2 error: {host}: no address"),
        });
    };

    let has_header = |name: &str| headers.iter().any(|(header, _)| header.eq_ignore_ascii_case(name));
    let mut head = format!("{method} {target} HTTP/1.1\r\n");
    if !has_header("host") {
        match url.port() {
            Some(port) => head.push_str(&format!("Host: {host}:{port}\r\n")),
            None => head.push_str(&format!("Host: {host}\r\n")),
        }
    }
    for (name, value) in headers {
        head.push_str(&format!("{name}: {value}\r\n"));
    }
    if !body.is_empty() && !has_header("content-length") {
        head.push_str(&format!("Content-Length: {}\r\n", body.len()));
    }
    head.push_str("Connection: close\r\n");
    head.push_str("\r\n");
    stream.set_write_timeout(remaining()?).map_err(io_error)?;
    stream.write_all(head.as_bytes()).map_err(io_error)?;
    stream.write_all(body).map_err(io_error)?;

    const MAX_HEAD_BYTES: usize = 1024 * 1024 + 8192 + 64;
    let mut raw: Vec<u8> = Vec::new();
    let mut chunk = vec![0u8; 64 * 1024];
    let mut eof = false;
    let mut read_more = |raw: &mut Vec<u8>, eof: &mut bool| -> Result<(), String> {
        loop {
            stream.set_read_timeout(remaining()?).map_err(io_error)?;
            match stream.read(&mut chunk) {
                Ok(0) => {
                    *eof = true;
                    return Ok(());
                }
                Ok(n) => {
                    raw.extend_from_slice(&chunk[..n]);
                    return Ok(());
                }
                Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
                Err(error) => return Err(format!("rt_http_request_v2 read error: {error}")),
            }
        }
    };

    // Response head; interim 1xx responses (other than 101) are skipped.
    let mut start = 0;
    let (status, reason, raw_headers, chunked, content_length, body_start) = loop {
        let Some(end) = find_bytes(&raw[start..], b"\r\n\r\n") else {
            if raw.len() - start > MAX_HEAD_BYTES {
                return Err("rt_http_request_v2: response headers exceed 1 MiB".to_string());
            }
            if eof {
                return Err("rt_http_request_v2 error: connection closed before response headers".to_string());
            }
            read_more(&mut raw, &mut eof)?;
            continue;
        };
        let head = String::from_utf8_lossy(&raw[start..start + end]).into_owned();
        let head = head.as_str();
        let (status_line, header_block) = head.split_once("\r\n").unwrap_or((head, ""));
        let mut parts = status_line.splitn(3, ' ');
        if !parts.next().is_some_and(|version| version.starts_with("HTTP/")) {
            return Err("rt_http_request_v2: invalid status line".to_string());
        }
        let status = match parts.next() {
            Some(code) if code.len() == 3 && code.bytes().all(|b| b.is_ascii_digit()) => {
                code.parse::<i64>().unwrap_or(-1)
            }
            _ => return Err("rt_http_request_v2: invalid status line".to_string()),
        };
        let body_start = start + end + 4;
        if (100..200).contains(&status) && status != 101 {
            start = body_start;
            continue;
        }
        let reason = parts.next().unwrap_or("").to_string();
        if reason.len() > 8192 {
            return Err("rt_http_request_v2: status reason exceeds 8 KiB".to_string());
        }
        let mut raw_headers = String::new();
        let mut chunked = false;
        let mut content_length = None;
        let lines: Vec<&str> = if header_block.is_empty() { Vec::new() } else { header_block.split("\r\n").collect() };
        if lines.len() > 1024 {
            return Err("rt_http_request_v2: too many response headers".to_string());
        }
        for line in lines {
            let Some((name, value)) = line.split_once(':') else {
                return Err("rt_http_request_v2: invalid response header".to_string());
            };
            let name = name.trim().to_ascii_lowercase();
            let value = value.trim();
            if name == "transfer-encoding" && value.to_ascii_lowercase().contains("chunked") {
                chunked = true;
            }
            if name == "content-length" {
                content_length = Some(
                    value
                        .parse::<usize>()
                        .map_err(|_| "rt_http_request_v2: invalid content-length".to_string())?,
                );
            }
            raw_headers.push_str(&format!("{name}: {value}\r\n"));
            if raw_headers.len() > 1024 * 1024 {
                return Err("rt_http_request_v2: response headers exceed 1 MiB".to_string());
            }
        }
        break (status, reason, raw_headers, chunked, content_length, body_start);
    };

    let too_large = || "rt_http_request_v2: response exceeds 64 MiB".to_string();
    let no_body = method.eq_ignore_ascii_case("HEAD") || status == 204 || status == 304;
    let body = if no_body {
        Vec::new()
    } else if chunked {
        loop {
            let data = &raw[body_start..];
            // A complete chunked message always ends with an empty line.
            if eof || data.ends_with(b"\r\n\r\n") {
                if let Some(decoded) = decode_chunked(data, max_body)? {
                    break decoded;
                }
                if eof {
                    return Err("rt_http_request_v2 read error: truncated chunked body".to_string());
                }
            }
            // Worst-case framing is 6 wire bytes per decoded byte (`1\r\nX\r\n`).
            if data.len() > max_body.saturating_mul(6) {
                return Err(too_large());
            }
            read_more(&mut raw, &mut eof)?;
        }
    } else if let Some(length) = content_length {
        if length > max_body {
            return Err(too_large());
        }
        while raw.len() - body_start < length {
            if eof {
                return Err("rt_http_request_v2 read error: truncated body".to_string());
            }
            read_more(&mut raw, &mut eof)?;
        }
        raw[body_start..body_start + length].to_vec()
    } else {
        while !eof {
            if raw.len() - body_start > max_body {
                return Err(too_large());
            }
            read_more(&mut raw, &mut eof)?;
        }
        raw[body_start..].to_vec()
    };
    if body.len() > max_body {
        return Err(too_large());
    }
    Ok((status, reason, raw_headers, body))
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

    const OK_RESPONSE: &[u8] = b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\nConnection: close\r\n\r\nok";

    /// Serve exactly one request on loopback at `path`, answer with `response`,
    /// and hand back the received request head (request line + headers) and body.
    fn serve_once(
        path: &str,
        response: &'static [u8],
    ) -> (String, std::sync::mpsc::Receiver<(String, Vec<u8>)>) {
        use std::io::{Read, Write};
        let listener = std::net::TcpListener::bind("127.0.0.1:0").expect("bind loopback");
        let url = format!("http://{}{path}", listener.local_addr().expect("addr"));
        let (tx, rx) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            let (mut stream, _) = listener.accept().expect("accept");
            let mut raw = Vec::new();
            let mut chunk = [0u8; 1024];
            let (head, body) = loop {
                let n = stream.read(&mut chunk).expect("read request");
                raw.extend_from_slice(&chunk[..n]);
                let Some(end) = raw.windows(4).position(|w| w == b"\r\n\r\n") else {
                    assert!(n > 0, "request ended before headers");
                    continue;
                };
                let head = String::from_utf8_lossy(&raw[..end]).to_string();
                let length = head
                    .to_ascii_lowercase()
                    .lines()
                    .find_map(|line| line.strip_prefix("content-length:").map(|v| v.trim().to_string()))
                    .map(|value| value.parse::<usize>().expect("content-length"))
                    .unwrap_or(0);
                if raw.len() >= end + 4 + length {
                    break (head, raw[end + 4..end + 4 + length].to_vec());
                }
                assert!(n > 0, "request ended before body");
            };
            stream.write_all(response).expect("write response");
            tx.send((head, body)).expect("send request");
        });
        (url, rx)
    }

    fn one_shot_server() -> (String, std::sync::mpsc::Receiver<(String, Vec<u8>)>) {
        serve_once("/obj", OK_RESPONSE)
    }

    fn tuple_fields(value: Value) -> Vec<Value> {
        let Value::Tuple(fields) = value else {
            panic!("expected HTTP v2 tuple")
        };
        assert!(matches!(&fields[4], Value::Str(message) if message.is_empty()), "{:?}", fields[4]);
        fields
    }

    fn recv_request(rx: std::sync::mpsc::Receiver<(String, Vec<u8>)>) -> (String, Vec<u8>) {
        rx.recv_timeout(std::time::Duration::from_secs(5)).expect("server saw request")
    }

    fn put_args(url: String, body: Value) -> Vec<Value> {
        vec![
            Value::text("PUT".to_string()),
            Value::text(url),
            Value::array(vec![Value::text("Content-Type: application/octet-stream".to_string())]),
            body,
            Value::Int(5000),
        ]
    }

    /// A pure-Simple `[u8]` literal reaches the interpreter as a boxed element
    /// array, not packed `ByteArray` storage. The extern ABI is `body: [u8]`, so
    /// both representations must send the identical octets.
    #[test]
    fn http_v2_accepts_boxed_u8_array_body() {
        let octets = [0u8, 128, 255, 65, 10];
        for body in [
            Value::array(octets.iter().map(|b| Value::Int(i64::from(*b))).collect::<Vec<_>>()),
            Value::array(Value::byte_array_values(&octets)),
        ] {
            let (url, received) = one_shot_server();
            let Value::Tuple(fields) = rt_http_request_v2(&put_args(url, body)).expect("tuple") else {
                panic!("expected HTTP v2 tuple")
            };
            assert!(
                matches!(&fields[4], Value::Str(message) if message.is_empty()),
                "{:?}",
                fields[4]
            );
            assert!(matches!(fields[0], Value::Int(200)), "{:?}", fields[0]);
            assert_eq!(fields[3].byte_array_view(), Some(&b"ok"[..]));
            let (_, sent) = recv_request(received);
            assert_eq!(sent, octets);
        }
    }

    /// Elements outside 0..=255 are not `[u8]`; refuse before any I/O.
    #[test]
    fn http_v2_rejects_out_of_range_array_body_before_io() {
        for bad in [Value::Int(256), Value::Int(-1), Value::text("x".to_string())] {
            let args = put_args(
                "http://127.0.0.1:9/".to_string(),
                Value::array(vec![Value::Int(1), bad]),
            );
            let value = rt_http_request_v2(&args).expect("typed failure");
            let Value::Tuple(ref fields) = value else {
                panic!("expected HTTP v2 tuple")
            };
            assert!(matches!(&fields[4], Value::Str(m) if m.as_str() == "rt_http_request_v2: body must be bytes"));
            assert_typed_error(value);
        }
    }

    /// An S3 key such as `dir/../direct.bin` is signed over the raw path
    /// (SigV4), so the request target must reach the wire byte-exact. ureq's
    /// WHATWG URL parser removes dot segments; the extern must not.
    #[test]
    fn http_v2_sends_dot_segment_path_verbatim() {
        let octets = [1u8, 2, 3, 250, 0];
        let (url, received) = serve_once("/bucket/dir/../direct.bin", OK_RESPONSE);
        let port = url.trim_start_matches("http://127.0.0.1:").split('/').next().unwrap().to_string();
        let fields = tuple_fields(rt_http_request_v2(&put_args(url, Value::byte_array(octets.to_vec()))).expect("tuple"));
        assert!(matches!(fields[0], Value::Int(200)), "{:?}", fields[0]);
        assert_eq!(fields[3].byte_array_view(), Some(&b"ok"[..]));
        let (head, body) = recv_request(received);
        let mut lines = head.lines();
        assert_eq!(lines.next(), Some("PUT /bucket/dir/../direct.bin HTTP/1.1"), "{head}");
        let lower = head.to_ascii_lowercase();
        assert!(lower.contains(&format!("\r\nhost: 127.0.0.1:{port}\r\n")), "{head}");
        assert!(lower.contains("\r\ncontent-type: application/octet-stream"), "{head}");
        assert!(lower.contains("\r\ncontent-length: 5"), "{head}");
        assert_eq!(body, octets);
    }

    /// Percent-encoded dot segments are dot segments to the URL parser too;
    /// they stay encoded on the wire. The query is kept and the fragment is
    /// never sent.
    #[test]
    fn http_v2_sends_encoded_dot_segment_verbatim_without_fragment() {
        let (url, received) = serve_once("/a/%2E%2e/b/./c?x=1&y=..#frag", OK_RESPONSE);
        let args = vec![
            Value::text("GET".to_string()),
            Value::text(url),
            Value::array(Vec::new()),
            Value::byte_array(Vec::new()),
            Value::Int(5000),
        ];
        let fields = tuple_fields(rt_http_request_v2(&args).expect("tuple"));
        assert!(matches!(fields[0], Value::Int(200)), "{:?}", fields[0]);
        let (head, body) = recv_request(received);
        assert_eq!(head.lines().next(), Some("GET /a/%2E%2e/b/./c?x=1&y=.. HTTP/1.1"), "{head}");
        assert!(body.is_empty());
    }

    /// The verbatim transport returns the same tuple shape as the ureq lane:
    /// reason text, lowercased raw header lines, and a de-chunked body.
    #[test]
    fn http_v2_dot_segment_path_decodes_chunked_response() {
        const CHUNKED: &[u8] = b"HTTP/1.1 201 Created\r\nX-Amz-Id: 7\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nok\r\n1;ext=1\r\n!\r\n0\r\n\r\n";
        let (url, received) = serve_once("/k/../v", CHUNKED);
        let fields = tuple_fields(rt_http_request_v2(&put_args(url, Value::byte_array(vec![9]))).expect("tuple"));
        assert!(matches!(fields[0], Value::Int(201)), "{:?}", fields[0]);
        assert!(matches!(&fields[1], Value::Str(r) if r.as_str() == "Created"), "{:?}", fields[1]);
        assert!(
            matches!(&fields[2], Value::Str(h) if h.as_str() == "x-amz-id: 7\r\ntransfer-encoding: chunked\r\n"),
            "{:?}",
            fields[2]
        );
        assert_eq!(fields[3].byte_array_view(), Some(&b"ok!"[..]));
        let (head, _) = recv_request(received);
        assert_eq!(head.lines().next(), Some("PUT /k/../v HTTP/1.1"), "{head}");
    }

    /// Only whole `.`/`..` segments (plain or `%2e`) route to the verbatim
    /// transport; dots inside a segment or in the query do not.
    #[test]
    fn http_v2_dot_segment_classification() {
        for target in ["/a/../b", "/a/./b", "/..", "/a/%2E%2e", "/a/.%2E/b", "/a\\..\\b"] {
            assert!(has_dot_segment(target), "{target}");
        }
        for target in ["/", "/a..b/c", "/.../x", "/a.b", "/obj?x=../y", "/.hidden"] {
            assert!(!has_dot_segment(target), "{target}");
        }
        assert_eq!(verbatim_request_target("http://h:1/a/../b?q=1#f").as_deref(), Some("/a/../b?q=1"));
        assert_eq!(verbatim_request_target("http://h:1?q").as_deref(), Some("/?q"));
        assert_eq!(verbatim_request_target("http://h").as_deref(), Some("/"));
        assert_eq!(verbatim_request_target("no-scheme"), None);
    }

    /// The url crate drops CR/LF/tab, so the raw target is checked itself:
    /// control or space bytes would split or corrupt the request line.
    #[test]
    fn http_v2_dot_segment_rejects_control_bytes_and_unsupported_headers_before_io() {
        for url in ["http://127.0.0.1:9/a/../b\r\nX-Evil: 1", "http://127.0.0.1:9/a/../b c", "http://127.0.0.1:9/a/..\t/b"] {
            let value = rt_http_request_v2(&put_args(url.to_string(), Value::byte_array(vec![1]))).expect("typed failure");
            let Value::Tuple(ref fields) = value else {
                panic!("expected HTTP v2 tuple")
            };
            assert!(matches!(&fields[4], Value::Str(m) if m.as_str() == "rt_http_request_v2: invalid URL"), "{url:?}: {:?}", fields[4]);
            assert_typed_error(value);
        }
        for header in ["Connection: keep-alive", "Transfer-Encoding: chunked"] {
            let args = vec![
                Value::text("PUT".to_string()),
                Value::text("http://127.0.0.1:9/a/../b".to_string()),
                Value::array(vec![Value::text(header.to_string())]),
                Value::byte_array(vec![1]),
                Value::Int(5000),
            ];
            assert_typed_error(rt_http_request_v2(&args).expect("typed failure"));
        }
        assert_typed_error(
            rt_http_request_v2(&put_args("http://u:p@127.0.0.1:9/a/../b".to_string(), Value::byte_array(vec![1])))
                .expect("typed failure"),
        );
    }

    /// Header order/replacement follows ureq's `set`; interim 1xx responses
    /// are skipped and chunked trailers are consumed.
    #[test]
    fn http_v2_dot_segment_header_semantics_interim_response_and_trailers() {
        const RESPONSE: &[u8] = b"HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n1\r\nA\r\n0\r\nX-T: 1\r\n\r\n";
        let (url, received) = serve_once("/a/../b", RESPONSE);
        let headers = ["X-Amz-Meta: a", "X-Amz-Meta: b", "Accept: 1", "Accept: 2"];
        let args = vec![
            Value::text("GET".to_string()),
            Value::text(url),
            Value::array(headers.iter().map(|h| Value::text(h.to_string())).collect::<Vec<_>>()),
            Value::byte_array(Vec::new()),
            Value::Int(5000),
        ];
        let fields = tuple_fields(rt_http_request_v2(&args).expect("tuple"));
        assert!(matches!(fields[0], Value::Int(200)), "{:?}", fields[0]);
        assert_eq!(fields[3].byte_array_view(), Some(&b"A"[..]));
        let (head, _) = recv_request(received);
        assert!(head.contains("\r\nX-Amz-Meta: a\r\nX-Amz-Meta: b\r\nAccept: 2\r\n"), "{head}");
        assert!(!head.contains("Accept: 1"), "{head}");
        assert!(head.ends_with("Connection: close"), "{head}");
    }

    /// Paths without dot segments keep the existing transport and wire form.
    #[test]
    fn http_v2_plain_path_and_query_unchanged() {
        let (url, received) = serve_once("/bucket/a/b.bin?partNumber=1", OK_RESPONSE);
        let fields = tuple_fields(rt_http_request_v2(&put_args(url, Value::byte_array(vec![7]))).expect("tuple"));
        assert!(matches!(fields[0], Value::Int(200)), "{:?}", fields[0]);
        let (head, body) = recv_request(received);
        assert_eq!(head.lines().next(), Some("PUT /bucket/a/b.bin?partNumber=1 HTTP/1.1"), "{head}");
        assert_eq!(body, vec![7]);
    }

    /// TLS goes through ureq, which cannot send a dot segment verbatim; refuse
    /// before I/O instead of silently sending a different (unsigned) path.
    #[test]
    fn http_v2_https_dot_segment_fails_closed_before_io() {
        let args = put_args("https://127.0.0.1:9/bucket/dir/../direct.bin".to_string(), Value::byte_array(vec![1]));
        let value = rt_http_request_v2(&args).expect("typed failure");
        let Value::Tuple(ref fields) = value else {
            panic!("expected HTTP v2 tuple")
        };
        assert!(
            matches!(&fields[4], Value::Str(m) if m.as_str().contains("dot-segment")),
            "{:?}",
            fields[4]
        );
        assert_typed_error(value);
    }
}
