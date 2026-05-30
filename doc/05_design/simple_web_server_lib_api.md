# Simple Web Server — Lightweight Lib API

> **Location:** `src/lib/nogc_sync_mut/http_server/`
> **Import:** `use std.nogc_sync_mut.http_server.*`
> **Full example using this lib:** `examples/simple_web_server/` ([design](simple_web_server_example.md))
> **Architecture overview:** [simple_web_server_split.md](simple_web_server_split.md)

## Quick Start

```simple
use std.nogc_sync_mut.http_server.{SimpleHttpServer, HttpRequest, HttpResponse, Router}

fn handle_hello(req: HttpRequest) -> HttpResponse:
    return HttpResponse.ok("Hello, World!")

fn handle_json(req: HttpRequest) -> HttpResponse:
    return HttpResponse.json("{\"status\": \"ok\"}")

fn main():
    var router = Router.new()
    router.get("/", handle_hello)
    router.get("/api/status", handle_json)

    var server = SimpleHttpServer.new("0.0.0.0", 8080, router)
    server.start()
```

## Types

### HttpMethod

```simple
enum HttpMethod:
    Get
    Post
    Put
    Delete
    Patch
    Head
    Options
```

### HttpStatus

```simple
enum HttpStatus:
    Ok              # 200
    Created         # 201
    NoContent       # 204
    MovedPermanently # 301
    Found           # 302
    NotModified     # 304
    BadRequest      # 400
    Unauthorized    # 401
    Forbidden       # 403
    NotFound        # 404
    MethodNotAllowed # 405
    InternalError   # 500
    NotImplemented  # 501
    BadGateway      # 502
    ServiceUnavailable # 503
```

### HttpRequest

```simple
class HttpRequest:
    method: HttpMethod
    path: text
    query: text            # raw query string after '?'
    headers: [(text, text)] # list of (name, value) pairs
    body: text
    remote_addr: text

    fn header(name: text) -> text?
    fn content_type() -> text
    fn content_length() -> i32
    fn query_param(name: text) -> text?
```

### HttpResponse

```simple
class HttpResponse:
    status: HttpStatus
    headers: [(text, text)]
    body: text

    # Constructors
    static fn ok(body: text) -> HttpResponse
    static fn json(body: text) -> HttpResponse
    static fn html(body: text) -> HttpResponse
    static fn redirect(url: text) -> HttpResponse
    static fn not_found() -> HttpResponse
    static fn error(status: HttpStatus, message: text) -> HttpResponse

    # Builder methods
    fn with_header(name: text, value: text) -> HttpResponse
    fn with_content_type(ct: text) -> HttpResponse
```

### Router

```simple
class Router:
    static fn new() -> Router

    # Route registration (exact match)
    fn get(path: text, handler: fn(HttpRequest) -> HttpResponse)
    fn post(path: text, handler: fn(HttpRequest) -> HttpResponse)
    fn put(path: text, handler: fn(HttpRequest) -> HttpResponse)
    fn delete(path: text, handler: fn(HttpRequest) -> HttpResponse)
    fn route(method: HttpMethod, path: text, handler: fn(HttpRequest) -> HttpResponse)

    # Prefix match (for sub-routers or catch-all)
    fn mount(prefix: text, handler: fn(HttpRequest) -> HttpResponse)

    # 404 handler override
    fn set_not_found(handler: fn(HttpRequest) -> HttpResponse)

    # Dispatch (called internally by server)
    fn dispatch(req: HttpRequest) -> HttpResponse
```

### SimpleHttpServer

```simple
class SimpleHttpServer:
    static fn new(host: text, port: i32, router: Router) -> SimpleHttpServer

    # Start the server (blocking accept loop, spawns thread per connection)
    fn start()

    # Start with a callback invoked after bind succeeds (for tests/logging)
    fn start_with_callback(on_ready: fn(text, i32))

    # Stop the server (sets running = false, next accept cycle exits)
    fn stop()
```

## Module Breakdown

| Module | Public Exports |
|--------|---------------|
| `types.spl` | `HttpMethod`, `HttpStatus`, `HttpRequest`, `HttpResponse` |
| `parser.spl` | `parse_request(stream: TcpStream) -> Result<HttpRequest, text>` |
| `response.spl` | `write_response(stream: TcpStream, resp: HttpResponse)`, `HttpResponse` constructors |
| `router.spl` | `Router` |
| `server.spl` | `SimpleHttpServer` |
| `__init__.spl` | Re-exports all public types and `SimpleHttpServer` |

## Middleware Pattern

The lightweight lib does not include a middleware chain, but middleware is trivially composable via handler wrapping:

```simple
fn with_logging(inner: fn(HttpRequest) -> HttpResponse) -> fn(HttpRequest) -> HttpResponse:
    return \req:
        val start = time_ms()
        val resp = inner(req)
        print "{req.method} {req.path} -> {resp.status} ({time_ms() - start}ms)"
        return resp
```

See `examples/simple_web_server/middleware.spl` ([design](simple_web_server_example.md)) for CORS, compression, and logging middleware built on this pattern.

## Error Model

- `parse_request()` returns `Result<HttpRequest, text>` — parse failures produce a descriptive error string.
- If parsing fails, the server sends a 400 Bad Request automatically.
- Handler exceptions are caught by the server and mapped to 500 Internal Error.
- No custom error types — text errors are sufficient for the lightweight tier.

## Dependencies

```
std.nogc_sync_mut.net.tcp   → TcpListener, TcpStream
std.common.text             → split, trim, starts_with, contains
```

No other stdlib dependencies. JSON, TLS, file I/O are opt-in via the caller.

## Relationship to Other Server Modules

| Module | Relationship |
|--------|-------------|
| `std.nogc_async_mut.http_server` | Full async server with middleware, CORS, CSRF, compression, metrics. Use when you need async I/O or the full middleware stack. |
| `std.nogc_sync_mut.io.tls_sffi` | TLS layer. Wrap `SimpleHttpServer` connections with TLS — see `examples/simple_web_server/tls.spl`. |
| `app.io.http_sffi` | SFFI-based HTTP server (Rust hyper). Different approach — uses extern runtime, not pure-Simple TCP. |
| `app.ui.web.server` | UI-specific sync server. Future refactor candidate to use this lib internally. |
