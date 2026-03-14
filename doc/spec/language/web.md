# Web Framework Specification

**Status:** Implementation
**Version:** 1.0
**Last Updated:** 2025-12-20

## Overview

The Simple Web Framework provides SSR-first web application development, building on the existing UI framework (`ui/*`) and networking layer (`host/net/*`).

## Architecture

```
HTTP Request
      │
      ▼
┌─────────────────────────────────────────────────────────────┐
│                      HttpServer                              │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐     │
│  │ TCP Accept  │ → │ Parse Request│ → │   Router    │     │
│  └─────────────┘    └─────────────┘    └──────┬──────┘     │
└──────────────────────────────────────────────┬──────────────┘
                                                │
                                    ┌───────────┴───────────┐
                                    ▼                       ▼
                            ┌─────────────┐         ┌─────────────┐
                            │ Middleware  │         │   Handler   │
                            │ (before)    │         │  Function   │
                            └──────┬──────┘         └──────┬──────┘
                                   │                       │
                                   └───────────┬───────────┘
                                               ▼
                                    ┌─────────────────┐
                                    │   UI Tree       │
                                    │  (ElementTree)  │
                                    └────────┬────────┘
                                             │
                                             ▼
                                    ┌─────────────────┐
                                    │  HtmlRenderer   │
                                    │  (SSR)          │
                                    └────────┬────────┘
                                             │
                                             ▼
                                    ┌─────────────────┐
                                    │ HttpResponse    │
                                    └─────────────────┘
```

## Module Structure

```
simple/std_lib/src/web/
├── __init__.spl              # Module manifest - exports public API
├── http/
│   ├── __init__.spl          # HTTP submodule
│   ├── request.spl           # HttpRequest parser
│   ├── response.spl          # HttpResponse builder
│   └── server.spl            # HttpServer loop
├── router.spl                # Router with path parameters
├── middleware.spl            # Middleware trait and pipeline
├── ssr.spl                   # SSR integration with ui/gui/html.spl
├── static.spl                # Static file serving
└── app.spl                   # WebApp builder (main entry)
```

---

## HTTP Types

### HttpMethod

```simple
pub enum HttpMethod:
    Get
    Post
    Put
    Delete
    Patch
    Head
    Options
    Connect
    Trace

impl HttpMethod:
    pub fn from_str(s: &str) -> Option[HttpMethod]
    pub fn to_str(self) -> &str
```

### HttpRequest

Parsed HTTP request from raw TCP bytes.

```simple
pub struct HttpRequest:
    method: HttpMethod
    path: str
    query: Dict[str, str]
    headers: Dict[str, str]
    body: Option[Bytes]
    version: str
    remote_addr: SocketAddr

impl HttpRequest:
    # Parse from TCP stream
    pub async fn parse(stream: &TcpStream) -> Result[HttpRequest, HttpError]

    # Accessors
    pub fn method(self) -> HttpMethod
    pub fn path(self) -> &str
    pub fn query_param(self, name: &str) -> Option[&str]
    pub fn header(self, name: &str) -> Option[&str]
    pub fn content_type(self) -> Option[&str]
    pub fn content_length(self) -> Option[u64]

    # Body parsing
    pub fn body_text(self) -> Result[str, HttpError]
    pub fn body_json[T: Deserialize](self) -> Result[T, HttpError]
    pub fn body_form(self) -> Result[Dict[str, str], HttpError]
```

### StatusCode

HTTP status codes with helpers.

```simple
pub enum StatusCode:
    # 2xx Success
    Ok = 200
    Created = 201
    Accepted = 202
    NoContent = 204

    # 3xx Redirect
    MovedPermanently = 301
    Found = 302
    SeeOther = 303
    NotModified = 304
    TemporaryRedirect = 307
    PermanentRedirect = 308

    # 4xx Client Error
    BadRequest = 400
    Unauthorized = 401
    Forbidden = 403
    NotFound = 404
    MethodNotAllowed = 405
    Conflict = 409
    Gone = 410
    UnprocessableEntity = 422
    TooManyRequests = 429

    # 5xx Server Error
    InternalServerError = 500
    NotImplemented = 501
    BadGateway = 502
    ServiceUnavailable = 503
    GatewayTimeout = 504

impl StatusCode:
    pub fn code(self) -> u16
    pub fn reason(self) -> &str
    pub fn is_success(self) -> bool
    pub fn is_redirect(self) -> bool
    pub fn is_client_error(self) -> bool
    pub fn is_server_error(self) -> bool
```

### HttpResponse

Fluent response builder.

```simple
pub struct HttpResponse:
    status: StatusCode
    headers: Dict[str, str]
    body: Option[Bytes]

impl HttpResponse:
    # Constructors
    pub fn new(status: StatusCode) -> HttpResponse
    pub fn ok() -> HttpResponse
    pub fn created() -> HttpResponse
    pub fn no_content() -> HttpResponse
    pub fn bad_request() -> HttpResponse
    pub fn unauthorized() -> HttpResponse
    pub fn forbidden() -> HttpResponse
    pub fn not_found() -> HttpResponse
    pub fn internal_error() -> HttpResponse

    # Redirects
    pub fn redirect(location: &str) -> HttpResponse
    pub fn redirect_permanent(location: &str) -> HttpResponse

    # Builder methods (fluent)
    pub fn status(self, status: StatusCode) -> HttpResponse
    pub fn header(self, name: &str, value: &str) -> HttpResponse
    pub fn content_type(self, mime: &str) -> HttpResponse

    # Body setters
    pub fn body(self, data: Bytes) -> HttpResponse
    pub fn text(self, text: &str) -> HttpResponse
    pub fn html(self, html: &str) -> HttpResponse
    pub fn json[T: Serialize](self, data: &T) -> HttpResponse

    # Serialization
    pub fn to_bytes(self) -> Bytes
    pub async fn send(self, stream: &TcpStream) -> Result[(), IoError]
```

### HttpError

Error types for HTTP operations.

```simple
pub enum HttpError:
    # Parsing errors
    InvalidRequestLine
    InvalidHeader
    InvalidMethod
    InvalidPath
    InvalidVersion

    # Body errors
    NoBody
    InvalidJson
    InvalidForm
    BodyTooLarge

    # Connection errors
    ConnectionClosed
    ReadTimeout
    WriteTimeout

    # Other
    IoError(IoError)
```

---

## HTTP Server

### ServerConfig

```simple
pub struct ServerConfig:
    addr: SocketAddr
    keep_alive: bool
    keep_alive_timeout: Duration
    max_connections: u32
    read_timeout: Duration
    write_timeout: Duration
    max_body_size: ByteCount

impl ServerConfig:
    pub fn new(addr: SocketAddr) -> ServerConfig
    pub fn bind_local(port: Port) -> ServerConfig

    # Builder methods
    pub fn keep_alive(self, enabled: bool) -> ServerConfig
    pub fn keep_alive_timeout(self, timeout: Duration) -> ServerConfig
    pub fn max_connections(self, max: u32) -> ServerConfig
    pub fn read_timeout(self, timeout: Duration) -> ServerConfig
    pub fn write_timeout(self, timeout: Duration) -> ServerConfig
    pub fn max_body_size(self, size: ByteCount) -> ServerConfig
```

### HttpServer

```simple
pub struct HttpServer:
    config: ServerConfig
    handler: fn(HttpRequest) -> async HttpResponse

impl HttpServer:
    pub fn new(config: ServerConfig) -> HttpServer
    pub fn handler(self, h: fn(HttpRequest) -> async HttpResponse) -> HttpServer
    pub async fn run(self) -> Result[(), IoError]
```

---

## Routing

### Route

```simple
pub struct Route:
    method: HttpMethod
    pattern: str
    handler: fn(Context) -> async HttpResponse
```

### RouteMatch

```simple
pub struct RouteMatch:
    handler: fn(Context) -> async HttpResponse
    params: Dict[str, str]
```

### Router

```simple
pub struct Router:
    routes: Array[Route]
    not_found: fn(Context) -> async HttpResponse

impl Router:
    pub fn new() -> Router

    # Add routes
    pub fn get(self, pattern: &str, handler: fn(Context) -> async HttpResponse) -> Router
    pub fn post(self, pattern: &str, handler: fn(Context) -> async HttpResponse) -> Router
    pub fn put(self, pattern: &str, handler: fn(Context) -> async HttpResponse) -> Router
    pub fn delete(self, pattern: &str, handler: fn(Context) -> async HttpResponse) -> Router
    pub fn patch(self, pattern: &str, handler: fn(Context) -> async HttpResponse) -> Router

    # Route groups
    pub fn group(self, prefix: &str, builder: fn(&mut Router)) -> Router

    # Fallback
    pub fn not_found(self, handler: fn(Context) -> async HttpResponse) -> Router

    # Matching
    pub fn match_route(self, request: &HttpRequest) -> RouteMatch
```

### Path Pattern Syntax

| Pattern | Example URL | Params |
|---------|-------------|--------|
| `/users` | `/users` | `{}` |
| `/users/:id` | `/users/42` | `{id: "42"}` |
| `/users/:id/posts/:post_id` | `/users/42/posts/5` | `{id: "42", post_id: "5"}` |
| `/files/*path` | `/files/a/b/c.txt` | `{path: "a/b/c.txt"}` |

---

## Middleware

### Middleware Trait

```simple
pub enum MiddlewareResult:
    Next                    # Continue to next middleware/handler
    Response(HttpResponse)  # Short-circuit with response

pub trait Middleware:
    async fn before(self, ctx: &mut Context) -> MiddlewareResult
    async fn after(self, ctx: &Context, response: &mut HttpResponse)
```

### Built-in Middleware

#### LoggerMiddleware

```simple
pub struct LoggerMiddleware:
    format: LogFormat

pub enum LogFormat:
    Common     # Apache common log format
    Combined   # Apache combined log format
    Json       # JSON structured logs

impl LoggerMiddleware:
    pub fn new() -> LoggerMiddleware
    pub fn format(self, fmt: LogFormat) -> LoggerMiddleware
```

#### CorsMiddleware

```simple
pub struct CorsMiddleware:
    allowed_origins: Array[str]
    allowed_methods: Array[HttpMethod]
    allowed_headers: Array[str]
    max_age: Duration

impl CorsMiddleware:
    pub fn new(origins: Array[str]) -> CorsMiddleware
    pub fn allow_all() -> CorsMiddleware
    pub fn methods(self, methods: Array[HttpMethod]) -> CorsMiddleware
    pub fn headers(self, headers: Array[str]) -> CorsMiddleware
    pub fn max_age(self, age: Duration) -> CorsMiddleware
```

---

## Handler Context

### Context

Request-scoped context passed to handlers.

```simple
pub struct Context:
    request: HttpRequest
    params: Dict[str, str]
    state: Dict[str, Any]

impl Context:
    # Request access
    pub fn request(self) -> &HttpRequest
    pub fn method(self) -> HttpMethod
    pub fn path(self) -> &str

    # Route parameters
    pub fn param(self, name: &str) -> Option[&str]
    pub fn param_u64(self, name: &str) -> Result[u64, ParseError]

    # Query parameters
    pub fn query(self, name: &str) -> Option[&str]

    # Headers
    pub fn header(self, name: &str) -> Option[&str]

    # Body
    pub fn body_text(self) -> Result[str, HttpError]
    pub fn body_json[T: Deserialize](self) -> Result[T, HttpError]

    # State
    pub fn get[T](self, key: &str) -> Option[&T]
    pub fn set[T](self, key: &str, value: T)
```

---

## SSR (Server-Side Rendering)

### RenderOptions

```simple
pub struct RenderOptions:
    title: str
    theme: Theme
    head_extra: str
    minify: bool
    include_hydration: bool

impl RenderOptions:
    pub fn new(title: &str) -> RenderOptions
    pub fn theme(self, theme: Theme) -> RenderOptions
    pub fn dark_theme(self) -> RenderOptions
    pub fn minified(self) -> RenderOptions
    pub fn no_hydration(self) -> RenderOptions
    pub fn head(self, html: &str) -> RenderOptions
```

### SsrRenderer

```simple
pub struct SsrRenderer:
    options: RenderOptions

impl SsrRenderer:
    pub fn new(options: RenderOptions) -> SsrRenderer
    pub fn render_page(self, tree: &ElementTree) -> str
    pub fn render_response(self, tree: &ElementTree) -> HttpResponse
```

### Convenience Functions

```simple
# Render UI tree to HTML string
pub fn render_to_html(tree: &ElementTree, title: &str) -> str

# Render UI tree to HTTP response
pub fn render_to_response(tree: &ElementTree, title: &str) -> HttpResponse
```

---

## Static File Serving

### StaticFileServer

```simple
pub struct StaticFileServer:
    root: FilePath
    index_file: str
    cache_control: str

impl StaticFileServer:
    pub fn new(root: FilePath) -> StaticFileServer
    pub fn index(self, file: &str) -> StaticFileServer
    pub fn cache(self, control: &str) -> StaticFileServer
    pub fn serve(self, path: &str) -> HttpResponse
```

### MIME Type Detection

```simple
pub fn detect_mime(path: &str) -> &str
```

| Extension | MIME Type |
|-----------|-----------|
| `.html` | `text/html` |
| `.css` | `text/css` |
| `.js` | `application/javascript` |
| `.json` | `application/json` |
| `.png` | `image/png` |
| `.jpg`, `.jpeg` | `image/jpeg` |
| `.gif` | `image/gif` |
| `.svg` | `image/svg+xml` |
| `.ico` | `image/x-icon` |
| `.woff`, `.woff2` | `font/woff2` |
| `.txt` | `text/plain` |
| `*` | `application/octet-stream` |

---

## WebApp Builder

### WebApp

Main application builder with fluent API.

```simple
pub struct WebApp:
    config: ServerConfig
    router: Router
    middleware: Array[Middleware]

impl WebApp:
    # Constructor
    pub fn new() -> WebApp

    # Configuration
    pub fn port(self, port: Port) -> WebApp
    pub fn addr(self, addr: SocketAddr) -> WebApp
    pub fn config(self, config: ServerConfig) -> WebApp

    # Middleware
    pub fn use_middleware(self, mw: Middleware) -> WebApp
    pub fn use_logger(self) -> WebApp
    pub fn use_cors(self, origins: Array[str]) -> WebApp

    # Routes
    pub fn get(self, pattern: &str, handler: fn(Context) -> async HttpResponse) -> WebApp
    pub fn post(self, pattern: &str, handler: fn(Context) -> async HttpResponse) -> WebApp
    pub fn put(self, pattern: &str, handler: fn(Context) -> async HttpResponse) -> WebApp
    pub fn delete(self, pattern: &str, handler: fn(Context) -> async HttpResponse) -> WebApp

    # Route groups
    pub fn group(self, prefix: &str, builder: fn(&mut Router)) -> WebApp

    # Static files
    pub fn static_files(self, url_prefix: &str, dir: FilePath) -> WebApp

    # Run server
    pub async fn run(self) -> Result[(), IoError]
```

---

## Example Application

```simple
use web.*
use ui.*
use ui.gui.theme.*

# Data model
struct User:
    id: u64
    name: str
    email: str

# Home page handler
async fn home_handler(ctx: Context) -> HttpResponse:
    let mut tree = ElementTree::new(ElementKind::Main)

    tree.root_mut()
        .with_class("container")
        .with_child(
            Element::heading(1, "Welcome to Simple Web")
        )
        .with_child(
            Element::paragraph("Build web apps with Simple language.")
        )
        .with_child(
            Element::button("Get Started")
                .with_class("primary")
        )

    return render_to_response(&tree, "Home | My App")

# User list page
async fn users_handler(ctx: Context) -> HttpResponse:
    let users = [
        User { id: 1, name: "Alice", email: "alice@example.com" },
        User { id: 2, name: "Bob", email: "bob@example.com" },
    ]

    let mut tree = ElementTree::new(ElementKind::Main)
    let root = tree.root_mut().with_class("container")

    root.with_child(Element::heading(1, "Users"))

    for user in users:
        root.with_child(
            Element::div()
                .with_class("card")
                .with_child(Element::heading(3, &user.name))
                .with_child(Element::paragraph(&user.email))
        )

    return render_to_response(&tree, "Users | My App")

# User detail page
async fn user_detail_handler(ctx: Context) -> HttpResponse:
    let id = ctx.param_u64("id")?

    # Fetch user (placeholder)
    let user = User { id: id, name: "Alice", email: "alice@example.com" }

    let mut tree = ElementTree::new(ElementKind::Article)
    tree.root_mut()
        .with_child(Element::heading(1, &user.name))
        .with_child(Element::paragraph(&f"ID: {user.id}"))
        .with_child(Element::paragraph(&f"Email: {user.email}"))

    return render_to_response(&tree, &f"{user.name} | My App")

# API: Get users as JSON
async fn api_users_handler(ctx: Context) -> HttpResponse:
    let users = [
        User { id: 1, name: "Alice", email: "alice@example.com" },
        User { id: 2, name: "Bob", email: "bob@example.com" },
    ]
    return HttpResponse::ok().json(&users)

# Main entry point
pub async fn main() -> i32:
    let app = WebApp::new()
        .port(3000_port)
        .use_logger()
        .use_cors(["*"])

        # HTML pages
        .get("/", home_handler)
        .get("/users", users_handler)
        .get("/users/:id", user_detail_handler)

        # API endpoints
        .group("/api", |router| {
            router
                .get("/users", api_users_handler)
                .get("/users/:id", api_user_handler)
                .post("/users", api_create_user_handler)
        })

        # Static files
        .static_files("/static", "public/")

    print("Server running at http://localhost:3000")

    match await app.run():
        case Ok(_): 0
        case Err(e):
            print(f"Server error: {e}")
            1
```

---

## Feature IDs

| ID | Feature | Phase |
|----|---------|-------|
| #520 | HTTP Request Parser | 1 |
| #521 | HTTP Response Builder | 1 |
| #522 | HTTP Server Loop | 1 |
| #523 | SSR Renderer Integration | 1 |
| #524 | Content-Type Detection | 1 |
| #525 | Path Router | 2 |
| #526 | Route Parameters | 2 |
| #527 | Route Groups | 2 |
| #528 | Static File Serving | 2 |
| #529 | Error Pages | 2 |
| #530 | WebApp Builder | 3 |
| #531 | Middleware Pipeline | 3 |
| #532 | Logger Middleware | 3 |
| #533 | CORS Middleware | 3 |
| #534 | Handler Context | 3 |

---

## Dependencies

**Uses existing modules:**
- `host.async_nogc_mut.net.tcp` - TCP sockets
- `ui.element` - Element types
- `ui.gui.html` - HTML renderer
- `ui.gui.theme` - Theme system
- `units.net` - Network types (Port, SocketAddr)
- `units.size` - Size units (ByteCount)
- `units.time` - Duration

**No new Rust FFI required** - builds entirely on existing TCP primitives.

---

## Related Documents

- [ui/element.spl](../../simple/std_lib/src/ui/element.spl) - Element types
- [ui/gui/html.spl](../../simple/std_lib/src/ui/gui/html.spl) - HTML renderer
- [host/net/tcp.spl](../../simple/std_lib/src/host/async_nogc_mut/net/tcp.spl) - TCP sockets
- [units/net.spl](../../simple/std_lib/src/units/net.spl) - Network types
