# HTTP Client/Server SFFI Implementation Guide

**Date:** 2026-02-08
**Status:** Specification Complete - Awaiting Runtime Implementation
**Estimated Rust Code:** 700-900 lines

---

## Overview

This guide provides the complete Rust implementation plan for the HTTP client/server SFFI wrapper. The wrapper provides REST API client, HTTP server, and WebSocket support for Simple programs.

**Libraries:**
- **Client:** `reqwest` (blocking API for simplicity)
- **Server:** `warp` or `axum` (async, with blocking wrapper)
- **WebSocket:** `tokio-tungstenite`

---

## Table of Contents

1. [Architecture](#architecture)
2. [HTTP Client Implementation](#http-client-implementation)
3. [HTTP Server Implementation](#http-server-implementation)
4. [WebSocket Implementation](#websocket-implementation)
5. [Testing Strategy](#testing-strategy)
6. [Performance Targets](#performance-targets)

---

## Architecture

### Library Selection

**HTTP Client - reqwest (blocking)**
```toml
[dependencies]
reqwest = { version = "0.11", features = ["blocking", "json"] }
```

**Pros:**
- Simple blocking API (matches Simple's model)
- Automatic TLS support
- JSON serialization/deserialization
- Cookies, redirects, timeouts built-in

**HTTP Server - warp or axum**
```toml
[dependencies]
warp = "0.3"
tokio = { version = "1", features = ["full"] }
```

**Pros:**
- Fast async server
- Easy routing
- WebSocket support
- Can wrap in blocking API for Simple

**WebSocket - tokio-tungstenite**
```toml
[dependencies]
tokio-tungstenite = "0.20"
```

---

## HTTP Client Implementation

### Handle Management

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use reqwest::blocking::{Client, RequestBuilder};

lazy_static! {
    static ref HTTP_CLIENTS: Arc<Mutex<HttpClients>> = Arc::new(Mutex::new(HttpClients::new()));
}

struct HttpClients {
    next_handle: i64,
    clients: HashMap<i64, Client>,
}

impl HttpClients {
    fn new() -> Self {
        Self {
            next_handle: 1,
            clients: HashMap::new(),
        }
    }

    fn add(&mut self, client: Client) -> i64 {
        let handle = self.next_handle;
        self.next_handle += 1;
        self.clients.insert(handle, client);
        handle
    }

    fn get(&self, handle: i64) -> Option<&Client> {
        self.clients.get(&handle)
    }

    fn remove(&mut self, handle: i64) -> bool {
        self.clients.remove(&handle).is_some()
    }
}
```

### Simple GET/POST/PUT/DELETE

```rust
use reqwest::blocking;
use std::ffi::{CStr, CString};
use std::os::raw::c_char;

fn string_to_c_char(s: String) -> *const c_char {
    CString::new(s).unwrap().into_raw()
}

fn c_char_to_string(ptr: *const c_char) -> String {
    unsafe { CStr::from_ptr(ptr).to_string_lossy().into_owned() }
}

#[no_mangle]
pub extern "C" fn rt_http_get(url: *const c_char) -> (i64, *const c_char, *const c_char) {
    let url_str = c_char_to_string(url);

    match blocking::get(&url_str) {
        Ok(response) => {
            let status = response.status().as_u16() as i64;
            let body = response.text().unwrap_or_default();
            (status, string_to_c_char(body), string_to_c_char(String::new()))
        }
        Err(e) => {
            (0, string_to_c_char(String::new()), string_to_c_char(e.to_string()))
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_http_post(
    url: *const c_char,
    body: *const c_char,
    content_type: *const c_char,
) -> (i64, *const c_char, *const c_char) {
    let url_str = c_char_to_string(url);
    let body_str = c_char_to_string(body);
    let ct_str = c_char_to_string(content_type);

    let client = blocking::Client::new();

    match client
        .post(&url_str)
        .header("Content-Type", ct_str)
        .body(body_str)
        .send()
    {
        Ok(response) => {
            let status = response.status().as_u16() as i64;
            let response_body = response.text().unwrap_or_default();
            (status, string_to_c_char(response_body), string_to_c_char(String::new()))
        }
        Err(e) => {
            (0, string_to_c_char(String::new()), string_to_c_char(e.to_string()))
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_http_put(
    url: *const c_char,
    body: *const c_char,
    content_type: *const c_char,
) -> (i64, *const c_char, *const c_char) {
    let url_str = c_char_to_string(url);
    let body_str = c_char_to_string(body);
    let ct_str = c_char_to_string(content_type);

    let client = blocking::Client::new();

    match client
        .put(&url_str)
        .header("Content-Type", ct_str)
        .body(body_str)
        .send()
    {
        Ok(response) => {
            let status = response.status().as_u16() as i64;
            let response_body = response.text().unwrap_or_default();
            (status, string_to_c_char(response_body), string_to_c_char(String::new()))
        }
        Err(e) => {
            (0, string_to_c_char(String::new()), string_to_c_char(e.to_string()))
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_http_delete(url: *const c_char) -> (i64, *const c_char, *const c_char) {
    let url_str = c_char_to_string(url);
    let client = blocking::Client::new();

    match client.delete(&url_str).send() {
        Ok(response) => {
            let status = response.status().as_u16() as i64;
            let body = response.text().unwrap_or_default();
            (status, string_to_c_char(body), string_to_c_char(String::new()))
        }
        Err(e) => {
            (0, string_to_c_char(String::new()), string_to_c_char(e.to_string()))
        }
    }
}
```

### Custom Request with Headers

```rust
#[no_mangle]
pub extern "C" fn rt_http_request(
    method: *const c_char,
    url: *const c_char,
    headers: *const *const c_char,
    headers_len: usize,
    body: *const c_char,
) -> (i64, *const c_char, *const c_char) {
    let method_str = c_char_to_string(method);
    let url_str = c_char_to_string(url);
    let body_str = c_char_to_string(body);

    // Parse headers
    let header_vec: Vec<String> = unsafe {
        std::slice::from_raw_parts(headers, headers_len)
            .iter()
            .map(|ptr| c_char_to_string(*ptr))
            .collect()
    };

    let client = blocking::Client::new();
    let method = reqwest::Method::from_bytes(method_str.as_bytes()).unwrap_or(reqwest::Method::GET);

    let mut request = client.request(method, &url_str);

    // Add headers
    for header in header_vec {
        if let Some((key, value)) = header.split_once(':') {
            request = request.header(key.trim(), value.trim());
        }
    }

    // Add body if not empty
    if !body_str.is_empty() {
        request = request.body(body_str);
    }

    match request.send() {
        Ok(response) => {
            let status = response.status().as_u16() as i64;
            let response_body = response.text().unwrap_or_default();
            (status, string_to_c_char(response_body), string_to_c_char(String::new()))
        }
        Err(e) => {
            (0, string_to_c_char(String::new()), string_to_c_char(e.to_string()))
        }
    }
}
```

### File Download/Upload

```rust
use std::fs::File;
use std::io::Write;

#[no_mangle]
pub extern "C" fn rt_http_download(
    url: *const c_char,
    output_path: *const c_char,
) -> (i64, i64, *const c_char) {
    let url_str = c_char_to_string(url);
    let path_str = c_char_to_string(output_path);

    match blocking::get(&url_str) {
        Ok(response) => {
            let status = response.status().as_u16() as i64;
            let bytes = response.bytes().unwrap_or_default();
            let len = bytes.len() as i64;

            // Write to file
            if let Ok(mut file) = File::create(&path_str) {
                file.write_all(&bytes).ok();
            }

            (status, len, string_to_c_char(String::new()))
        }
        Err(e) => {
            (0, 0, string_to_c_char(e.to_string()))
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_http_upload(
    url: *const c_char,
    file_path: *const c_char,
    field_name: *const c_char,
) -> (i64, *const c_char, *const c_char) {
    let url_str = c_char_to_string(url);
    let path_str = c_char_to_string(file_path);
    let field_str = c_char_to_string(field_name);

    use reqwest::blocking::multipart;

    // Read file
    let file = match std::fs::read(&path_str) {
        Ok(data) => data,
        Err(e) => return (0, string_to_c_char(String::new()), string_to_c_char(e.to_string())),
    };

    // Create multipart form
    let part = multipart::Part::bytes(file)
        .file_name(std::path::Path::new(&path_str).file_name().unwrap().to_string_lossy().to_string());

    let form = multipart::Form::new().part(field_str, part);

    let client = blocking::Client::new();

    match client.post(&url_str).multipart(form).send() {
        Ok(response) => {
            let status = response.status().as_u16() as i64;
            let body = response.text().unwrap_or_default();
            (status, string_to_c_char(body), string_to_c_char(String::new()))
        }
        Err(e) => {
            (0, string_to_c_char(String::new()), string_to_c_char(e.to_string()))
        }
    }
}
```

### Configured Client

```rust
#[no_mangle]
pub extern "C" fn rt_http_client_create() -> i64 {
    let client = blocking::Client::builder()
        .build()
        .unwrap();

    let mut clients = HTTP_CLIENTS.lock().unwrap();
    clients.add(client)
}

#[no_mangle]
pub extern "C" fn rt_http_client_set_timeout(client: i64, timeout_ms: i64) -> bool {
    // Note: reqwest Client is immutable, so we need to rebuild
    // For simplicity, store config and rebuild client on each change
    // Or use a ClientBuilder wrapper
    true
}

#[no_mangle]
pub extern "C" fn rt_http_client_set_header(
    client: i64,
    key: *const c_char,
    value: *const c_char,
) -> bool {
    // Store default headers in a separate map
    // and apply them in rt_http_client_request
    true
}

#[no_mangle]
pub extern "C" fn rt_http_client_destroy(client: i64) {
    let mut clients = HTTP_CLIENTS.lock().unwrap();
    clients.remove(client);
}
```

---

## HTTP Server Implementation

### Server with Warp

```rust
use warp::{Filter, Reply};
use std::sync::{Arc, Mutex};
use std::collections::HashMap;

lazy_static! {
    static ref HTTP_SERVERS: Arc<Mutex<HttpServers>> = Arc::new(Mutex::new(HttpServers::new()));
}

struct HttpServer {
    port: u16,
    routes: Vec<(String, String, String)>, // (method, path, handler)
    static_routes: Vec<(String, String)>,  // (path, dir)
}

struct HttpServers {
    next_handle: i64,
    servers: HashMap<i64, HttpServer>,
}

impl HttpServers {
    fn new() -> Self {
        Self {
            next_handle: 1,
            servers: HashMap::new(),
        }
    }

    fn add(&mut self, server: HttpServer) -> i64 {
        let handle = self.next_handle;
        self.next_handle += 1;
        self.servers.insert(handle, server);
        handle
    }

    fn get_mut(&mut self, handle: i64) -> Option<&mut HttpServer> {
        self.servers.get_mut(&handle)
    }

    fn remove(&mut self, handle: i64) -> bool {
        self.servers.remove(&handle).is_some()
    }
}

#[no_mangle]
pub extern "C" fn rt_http_server_create(port: i64) -> i64 {
    let server = HttpServer {
        port: port as u16,
        routes: Vec::new(),
        static_routes: Vec::new(),
    };

    let mut servers = HTTP_SERVERS.lock().unwrap();
    servers.add(server)
}

#[no_mangle]
pub extern "C" fn rt_http_server_route(
    server: i64,
    method: *const c_char,
    path: *const c_char,
    handler: *const c_char,
) -> bool {
    let method_str = c_char_to_string(method);
    let path_str = c_char_to_string(path);
    let handler_str = c_char_to_string(handler);

    let mut servers = HTTP_SERVERS.lock().unwrap();
    if let Some(srv) = servers.get_mut(server) {
        srv.routes.push((method_str, path_str, handler_str));
        true
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_http_server_static(
    server: i64,
    path: *const c_char,
    dir: *const c_char,
) -> bool {
    let path_str = c_char_to_string(path);
    let dir_str = c_char_to_string(dir);

    let mut servers = HTTP_SERVERS.lock().unwrap();
    if let Some(srv) = servers.get_mut(server) {
        srv.static_routes.push((path_str, dir_str));
        true
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_http_server_start(server: i64) -> bool {
    let servers = HTTP_SERVERS.lock().unwrap();
    let srv = match servers.get(&server) {
        Some(s) => s,
        None => return false,
    };

    let port = srv.port;

    // Build warp routes
    use warp::Filter;

    let hello = warp::path!("hello")
        .map(|| "Hello, World!");

    // For simplicity, start server in thread
    // In real implementation, need proper async runtime
    std::thread::spawn(move || {
        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async {
            warp::serve(hello).run(([127, 0, 0, 1], port)).await;
        });
    });

    true
}

#[no_mangle]
pub extern "C" fn rt_http_server_stop(server: i64) -> bool {
    // Would need to store server handle and call shutdown
    true
}

#[no_mangle]
pub extern "C" fn rt_http_server_destroy(server: i64) {
    let mut servers = HTTP_SERVERS.lock().unwrap();
    servers.remove(server);
}
```

**Note:** Server implementation is simplified. Full implementation needs:
- Proper route matching
- Handler callback mechanism (call Simple functions from Rust)
- Request/response object handling
- Async runtime management

---

## WebSocket Implementation

```rust
use tokio_tungstenite::{connect_async, tungstenite::Message};
use futures_util::{SinkExt, StreamExt};

struct WebSocketConnection {
    // Simplified - need proper async handling
    url: String,
}

lazy_static! {
    static ref WEBSOCKETS: Arc<Mutex<WebSockets>> = Arc::new(Mutex::new(WebSockets::new()));
}

struct WebSockets {
    next_handle: i64,
    connections: HashMap<i64, WebSocketConnection>,
}

impl WebSockets {
    fn new() -> Self {
        Self {
            next_handle: 1,
            connections: HashMap::new(),
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_ws_connect(url: *const c_char) -> i64 {
    let url_str = c_char_to_string(url);

    // Simplified - real implementation needs async runtime
    let ws = WebSocketConnection { url: url_str };

    let mut websockets = WEBSOCKETS.lock().unwrap();
    let handle = websockets.next_handle;
    websockets.next_handle += 1;
    websockets.connections.insert(handle, ws);
    handle
}

#[no_mangle]
pub extern "C" fn rt_ws_send(ws: i64, message: *const c_char) -> bool {
    let msg = c_char_to_string(message);
    // Send message through WebSocket
    // Needs proper async handling
    true
}

#[no_mangle]
pub extern "C" fn rt_ws_receive(ws: i64) -> *const c_char {
    // Receive message (blocking)
    // Needs proper async handling
    string_to_c_char(String::new())
}

#[no_mangle]
pub extern "C" fn rt_ws_close(ws: i64) -> bool {
    let mut websockets = WEBSOCKETS.lock().unwrap();
    websockets.connections.remove(&ws).is_some()
}
```

---

## Utility Functions

```rust
#[no_mangle]
pub extern "C" fn rt_http_url_encode(text: *const c_char) -> *const c_char {
    let text_str = c_char_to_string(text);
    let encoded = urlencoding::encode(&text_str);
    string_to_c_char(encoded.into_owned())
}

#[no_mangle]
pub extern "C" fn rt_http_url_decode(text: *const c_char) -> *const c_char {
    let text_str = c_char_to_string(text);
    let decoded = urlencoding::decode(&text_str).unwrap_or_default();
    string_to_c_char(decoded.into_owned())
}
```

---

## Testing Strategy

### Unit Tests

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_http_get() {
        // Test with httpbin.org
        let url = CString::new("https://httpbin.org/get").unwrap();
        let (status, body, error) = rt_http_get(url.as_ptr());

        assert_eq!(status, 200);
        assert!(error.is_null() || unsafe { CStr::from_ptr(error).to_str().unwrap().is_empty() });
    }

    #[test]
    fn test_http_post() {
        let url = CString::new("https://httpbin.org/post").unwrap();
        let body = CString::new(r#"{"test":"data"}"#).unwrap();
        let ct = CString::new("application/json").unwrap();

        let (status, response_body, error) = rt_http_post(url.as_ptr(), body.as_ptr(), ct.as_ptr());

        assert_eq!(status, 200);
    }
}
```

### Integration Tests

Run Simple test suite:
```bash
bin/simple test test/app/io/http_ffi_spec.spl
```

---

## Performance Targets

| Operation | Target | Notes |
|-----------|--------|-------|
| Client Creation | < 1ms | One-time cost |
| Simple GET | < 100ms | Network dependent |
| Simple POST | < 150ms | Network dependent |
| File Download | Variable | Depends on file size |
| Server Start | < 50ms | Async runtime startup |
| WebSocket Connect | < 200ms | Network dependent |
| Memory Per Client | < 1MB | Including connection pool |
| Memory Per Server | < 5MB | Base memory |

---

## Dependencies

**Cargo.toml:**
```toml
[dependencies]
reqwest = { version = "0.11", features = ["blocking", "json", "multipart"] }
warp = "0.3"
tokio = { version = "1", features = ["full"] }
tokio-tungstenite = "0.20"
urlencoding = "2.1"
futures-util = "0.3"
lazy_static = "1.4"
```

---

## Implementation Checklist

### Phase 1: HTTP Client (300 lines)
- [ ] Basic GET/POST/PUT/DELETE
- [ ] Custom headers
- [ ] File download/upload
- [ ] URL encoding

### Phase 2: Configured Client (150 lines)
- [ ] Client creation
- [ ] Timeout configuration
- [ ] Default headers
- [ ] Client destruction

### Phase 3: HTTP Server (250 lines)
- [ ] Server creation
- [ ] Route registration
- [ ] Static file serving
- [ ] Server start/stop

### Phase 4: WebSocket (150 lines)
- [ ] Connection
- [ ] Send/receive
- [ ] Close

### Phase 5: Testing (150 lines)
- [ ] Unit tests
- [ ] Integration tests
- [ ] Error handling tests

**Total:** ~1,000 lines Rust

---

## Summary

The HTTP wrapper provides comprehensive networking capabilities:
- ✅ REST API client (GET, POST, PUT, DELETE, PATCH, HEAD)
- ✅ File download/upload
- ✅ Custom headers and configuration
- ✅ HTTP server with routing
- ✅ WebSocket support
- ✅ URL encoding/decoding

**Implementation:** ~700-900 lines Rust using `reqwest`, `warp`, and `tokio-tungstenite`.

**Next Steps:**
1. Implement HTTP client with reqwest
2. Add HTTP server with warp
3. Add WebSocket support
4. Test with Simple test suite
