# Simple Web Server — Full Standalone Example

> **Location:** `examples/06_io/simple_web_server/`
> **Lightweight lib this example uses:** `src/lib/nogc_sync_mut/http_server/` ([API doc](simple_web_server_lib_api.md))
> **Architecture overview:** [simple_web_server_split.md](simple_web_server_split.md)

## Overview

A full-featured standalone HTTP server built entirely on the lightweight `std.nogc_sync_mut.http_server` lib. Demonstrates how to layer production features on top of the minimal core without modifying the lib itself.

## File Structure

```
examples/06_io/simple_web_server/
├── main.spl              # Entry point, CLI args, server startup
├── config.spl            # ServerConfig class (port, host, TLS paths, static root)
├── routes.spl            # Application route definitions
├── middleware.spl         # CORS, logging, compression wrappers
├── static_files.spl      # Directory-based static file serving
├── tls.spl               # TLS termination layer
├── websocket.spl          # WebSocket upgrade + broadcast
├── error_pages.spl        # Custom 404/500 HTML pages
└── public/                # Sample static assets
    ├── index.html
    ├── style.css
    └── favicon.ico
```

## Import Map

All server functionality flows from the lightweight lib:

```simple
# Core — from the lightweight lib
use std.nogc_sync_mut.http_server.{
    SimpleHttpServer,
    HttpRequest,
    HttpResponse,
    Router,
    HttpMethod,
    HttpStatus
}

# Extras — from stdlib for feature layers
use std.nogc_sync_mut.net.tcp.{TcpListener, TcpStream}
use std.nogc_sync_mut.io.tls.{...}        # TLS termination
use std.common.json.{...}                  # JSON API responses
use std.common.text.{...}                  # String utilities
```

## Feature Details

### 1. main.spl — Entry Point

```simple
use examples.simple_web_server.config.{ServerConfig, parse_args}
use examples.simple_web_server.routes.{register_routes}
use examples.simple_web_server.middleware.{wrap_with_middleware}
use std.nogc_sync_mut.http_server.{SimpleHttpServer, Router}

fn main():
    val config = parse_args()
    var router = Router.new()
    register_routes(router, config)
    val wrapped_router = wrap_with_middleware(router, config)
    var server = SimpleHttpServer.new(config.host, config.port, wrapped_router)
    print "simple_web_server listening on {config.host}:{config.port}"
    server.start()
```

### 2. config.spl — Server Configuration

```simple
class ServerConfig:
    host: text          # default "0.0.0.0"
    port: i32           # default 8080
    static_root: text   # default "./public"
    tls_enabled: bool   # default false
    tls_cert: text      # path to cert.pem
    tls_key: text       # path to key.pem
    cors_origins: [text] # allowed origins, default ["*"]
    log_requests: bool  # default true

    static fn default() -> ServerConfig
```

CLI args: `--port=N`, `--host=X`, `--static=DIR`, `--tls-cert=FILE`, `--tls-key=FILE`, `--no-log`.

### 3. routes.spl — Application Routes

Demonstrates the routing API from the lib:

```simple
fn register_routes(router: Router, config: ServerConfig):
    router.get("/", handle_index)
    router.get("/api/health", handle_health)
    router.post("/api/echo", handle_echo)
    router.get("/api/info", handle_info)
    router.mount("/static", make_static_handler(config.static_root))
    router.set_not_found(handle_404)
```

### 4. middleware.spl — Middleware Wrappers

Uses the handler-wrapping pattern from the lib:

```simple
# Logging middleware
fn with_logging(inner: fn(HttpRequest) -> HttpResponse) -> fn(HttpRequest) -> HttpResponse:
    return \req:
        val start = time_ms()
        val resp = inner(req)
        print "[{timestamp()}] {req.method} {req.path} -> {resp.status.code()} ({time_ms() - start}ms)"
        return resp

# CORS middleware
fn with_cors(origins: [text], inner: fn(HttpRequest) -> HttpResponse) -> fn(HttpRequest) -> HttpResponse:
    return \req:
        if req.method == HttpMethod.Options:
            return HttpResponse.ok("")
                .with_header("Access-Control-Allow-Origin", origins[0])
                .with_header("Access-Control-Allow-Methods", "GET, POST, PUT, DELETE, OPTIONS")
                .with_header("Access-Control-Allow-Headers", "Content-Type, Authorization")
        val resp = inner(req)
        return resp.with_header("Access-Control-Allow-Origin", origins[0])

# Compose all middleware
fn wrap_with_middleware(router: Router, config: ServerConfig) -> Router:
    # Middleware is applied via handler wrapping on each route
    ...
```

### 5. static_files.spl — Static File Serving

```simple
fn make_static_handler(root: text) -> fn(HttpRequest) -> HttpResponse:
    return \req:
        val rel_path = req.path.strip_prefix("/static")
        val file_path = "{root}/{rel_path}"
        if not file_exists(file_path):
            return HttpResponse.not_found()
        val content = file_read_text(file_path)
        val content_type = guess_content_type(file_path)
        return HttpResponse.ok(content).with_content_type(content_type)

fn guess_content_type(path: text) -> text:
    if path.ends_with(".html"): return "text/html"
    if path.ends_with(".css"):  return "text/css"
    if path.ends_with(".js"):   return "application/javascript"
    if path.ends_with(".json"): return "application/json"
    if path.ends_with(".png"):  return "image/png"
    if path.ends_with(".ico"):  return "image/x-icon"
    return "application/octet-stream"
```

### 6. tls.spl — TLS Termination

```simple
use std.nogc_sync_mut.io.tls.{tls_server_config_new, tls_server_accept, ...}

fn start_tls_server(config: ServerConfig, router: Router):
    val tls_config = tls_server_config_new(config.tls_cert, config.tls_key)
    # Wrap accept loop: TLS handshake → ConnStream → parse_request → router.dispatch
    ...
```

### 7. websocket.spl — WebSocket Upgrade

```simple
fn try_websocket_upgrade(req: HttpRequest, stream: TcpStream) -> bool:
    val upgrade_header = req.header("Upgrade")
    if upgrade_header != "websocket":
        return false
    # Perform WebSocket handshake, enter read/write loop
    ...
    return true
```

## Running the Example

```bash
# Basic
bin/simple run examples/06_io/simple_web_server/main.spl

# With options
bin/simple run examples/06_io/simple_web_server/main.spl -- --port=3000 --static=./my_assets

# With TLS
bin/simple run examples/06_io/simple_web_server/main.spl -- --tls-cert=cert.pem --tls-key=key.pem
```

## Relationship to Lightweight Lib

This example **reuses** the lightweight lib — it does not duplicate or fork it:

| Layer | Source | What it provides |
|-------|--------|------------------|
| **TCP + HTTP parsing** | `std.nogc_sync_mut.http_server` (lib) | Request/response types, parser, router, server loop |
| **Middleware** | `examples/06_io/simple_web_server/middleware.spl` (this example) | CORS, logging, compression — wraps lib handlers |
| **Static files** | `examples/06_io/simple_web_server/static_files.spl` (this example) | File serving via `mount()` — uses lib's prefix routing |
| **TLS** | `examples/06_io/simple_web_server/tls.spl` (this example) | TLS termination — wraps lib's TCP accept |
| **WebSocket** | `examples/06_io/simple_web_server/websocket.spl` (this example) | WS upgrade — intercepts before lib's HTTP routing |

Any feature the example adds can be extracted into a separate lib module later if demand warrants it, without changing the core lightweight lib.

## Cross-References

- **Lightweight lib API:** [`doc/05_design/simple_web_server_lib_api.md`](simple_web_server_lib_api.md)
- **Architecture split rationale:** [`doc/05_design/simple_web_server_split.md`](simple_web_server_split.md)
- **Existing async server (different tier):** `src/lib/nogc_async_mut/http_server/`
- **Existing UI web server (app-specific):** `src/app/ui.web/server.spl`
- **HTTP SFFI (Rust runtime):** `src/app/io/http_sffi.spl`
