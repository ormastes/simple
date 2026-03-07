# Web Framework and HTTP Guide

Covers the SimpleWeb server-side framework (routing, controllers, middleware, services) and the HTTP client/server SFFI layer.

---

## Architecture

```
Router (path -> controller.action)
    |
    v
Controllers (page / resource / API)
    |
    v
Services (business logic, DB access)
    |
    v
.sui Page (SSR)  or  JSON Response
```

---

## Routing

Routes are defined in `config/routes.spl`:

```spl
use simpleweb.routing.*

routes:
    get  "/"           => HomeController.index
    get  "/about"      => HomeController.about

    # RESTful resources (generates index, show, new, create, edit, update, destroy)
    resources "users"

    # Nested resources
    resources "posts":
        resources "comments"

    # API namespace
    namespace "/api/v1":
        get  "/users"      => Api.UsersController.list
        post "/users"      => Api.UsersController.create
        get  "/users/:id"  => Api.UsersController.get

    # Catch-all
    get "/*path" => ErrorController.not_found
```

### Path and Query Parameters

```spl
# Route: GET /users/:id/posts/:post_id
fn show(req):
    val user_id = req.params["id"]
    val post_id = req.params["post_id"]

# URL: /search?q=hello&page=2
fn search(req):
    val query = req.query["q"] or ""
    val page = req.query["page"].parse_int() or 1
```

---

## Controllers

### Page Controller (SSR)

```spl
class UsersController:
    @inject
    let user_service: UserService

    fn index(req) -> Response:
        let users = user_service.list_all()
        return page({ users: users })

    fn show(req) -> Response:
        let id = req.params["id"].parse_int()?
        let user = user_service.find(id)?
        return page("users/Show", { user: user })

    fn create(req) -> Response:
        let data = req.body.parse_json()?
        let user = user_service.create(data)?
        return redirect("/users/" + user.id)
```

### API Controller (JSON)

```spl
class UsersController:
    @inject
    let user_service: UserService

    fn list(req) -> Response:
        let users = user_service.list_all()
        return json(users)

    fn get(req) -> Response:
        let id = req.params["id"].parse_int()?
        match user_service.find(id):
            Some(user) => json(user)
            None => json_error(404, "User not found")

    fn create(req) -> Response:
        let data = req.body.parse_json()?
        match user_service.create(data):
            Ok(user) => json(user, status=201)
            Err(e) => json_error(400, e.message)
```

### Response Helpers

```spl
page(props)                    # Implicit view from controller/action
page("path/View", props)       # Explicit view
json(data)                     # 200 OK
json(data, status=201)         # Custom status
json_error(status, message)    # Error response
redirect(url)                  # 302 Found
text(content)                  # text/plain
html(content)                  # text/html
file(path)                     # File download
stream(iterator)               # Streaming response
```

---

## Middleware

```spl
@middleware
class AuthMiddleware:
    fn call(req, next) -> Response:
        match get_session(req):
            Some(session) if session.valid():
                req.context["user"] = session.user
                next(req)
            _ =>
                redirect("/login")
```

Apply middleware in routes:

```spl
routes:
    use AuthMiddleware          # Global
    use LoggingMiddleware

    namespace "/admin":
        use AdminAuthMiddleware # Scoped
        get "/" => AdminController.dashboard
```

---

## Services and Dependency Injection

```spl
@service
class UserService:
    @inject
    let db: Database

    @inject
    let cache: Cache

    fn list_all() -> List[User]:
        cache.get_or_set("users:all", fn():
            db.query("SELECT * FROM users")
        )

    fn create(data: Dict) -> Result[User, Error]:
        validate_user(data)?
        let user = db.insert("users", data)?
        cache.delete("users:all")
        Ok(user)
```

Manual DI registration:

```spl
services:
    bind(Database).to(PostgresDatabase)
    bind(Cache).to(RedisCache)
```

---

## Configuration

### web_app.toml

```toml
[app]
name = "myapp"
env_default = "dev"

[config]
files = ["config/app.toml", "config/app.{env}.toml"]
env_prefix = "APP_"

[starter]
web = true
json = true
health = true
metrics = true
```

Config priority (highest to lowest):
1. CLI arguments (`--port=8080`)
2. Environment variables (`APP_PORT=8080`)
3. `config/app.{env}.toml`
4. `config/app.toml`

### Health and Metrics

When starters are enabled:
- `GET /health` -- Liveness check
- `GET /health/ready` -- Readiness (DB, cache)
- `GET /metrics` -- Prometheus-format metrics

---

## HTTP Client (SFFI)

The HTTP client uses `reqwest` (blocking API) under the hood.

### Simple Requests

```simple
extern fn rt_http_get(url: text) -> (i64, text, text)
extern fn rt_http_post(url: text, body: text, content_type: text) -> (i64, text, text)
extern fn rt_http_put(url: text, body: text, content_type: text) -> (i64, text, text)
extern fn rt_http_delete(url: text) -> (i64, text, text)
```

Return tuple: `(status_code, response_body, error_message)`. Status 0 indicates a connection error.

### File Transfer

```simple
extern fn rt_http_download(url: text, output_path: text) -> (i64, i64, text)
extern fn rt_http_upload(url: text, file_path: text, field_name: text) -> (i64, text, text)
```

### Custom Requests with Headers

```simple
extern fn rt_http_request(
    method: text, url: text,
    headers: [text], headers_len: i64,
    body: text
) -> (i64, text, text)
```

### URL Encoding

```simple
extern fn rt_http_url_encode(text: text) -> text
extern fn rt_http_url_decode(text: text) -> text
```

---

## HTTP Server (SFFI)

The HTTP server uses `warp` with a blocking wrapper.

```simple
extern fn rt_http_server_create(port: i64) -> i64
extern fn rt_http_server_route(server: i64, method: text, path: text, handler: text) -> bool
extern fn rt_http_server_static(server: i64, path: text, dir: text) -> bool
extern fn rt_http_server_start(server: i64) -> bool
extern fn rt_http_server_stop(server: i64) -> bool
extern fn rt_http_server_destroy(server: i64)
```

---

## WebSocket (SFFI)

WebSocket support uses `tokio-tungstenite`:

```simple
extern fn rt_ws_connect(url: text) -> i64
extern fn rt_ws_send(ws: i64, message: text) -> bool
extern fn rt_ws_receive(ws: i64) -> text
extern fn rt_ws_close(ws: i64) -> bool
```

---

## Project Structure

```
myapp/
  web_app.toml
  config/
    app.toml, app.dev.toml, app.prod.toml
    routes.spl
    services.spl
  app/
    controllers/
    services/
    middleware/
    ui/                     # .sui pages (see ui.md)
    logic/                  # .spl page logic
  public/assets/
  test/
```

---

## CLI Tools

```bash
simple web serve                     # Start dev server
simple web serve --port=3000         # Custom port
simple web routes                    # List all routes
simple web generate controller Users # Scaffold controller
simple web build                     # Build for production
```

---

## Related Files

- UI framework: `doc/guide/library/ui.md`
- HTTP SFFI: `src/app/io/http_ffi.spl`
- Web framework guide: `doc/guide/apps/web.md`
