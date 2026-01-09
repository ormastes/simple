# SimpleWeb Framework Specification

Routing, controllers, API endpoints, and server configuration for Simple web applications.

> **Related Document**: For UI templates (`.sui` files), SSR rendering, and client components, see `doc/ui.md`. This document focuses on the **server-side infrastructure**.

---

## 1. Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                      SimpleWeb Stack                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                      Router                              │   │
│  │              path → controller.action                    │   │
│  └───────────────────────────┬─────────────────────────────┘   │
│                              │                                  │
│              ┌───────────────┼───────────────┐                  │
│              ▼               ▼               ▼                  │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐          │
│  │  Controller  │  │  Controller  │  │     API      │          │
│  │   (page)     │  │  (resource)  │  │  (json)      │          │
│  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘          │
│         │                 │                 │                   │
│         ▼                 ▼                 ▼                   │
│  ┌──────────────────────────────────────────────────────┐      │
│  │                     Services                          │      │
│  │            (business logic, DB access)                │      │
│  └──────────────────────────────────────────────────────┘      │
│         │                                                       │
│         ▼                                                       │
│  ┌──────────────┐     ┌──────────────┐                         │
│  │  .sui Page   │     │  JSON/API    │                         │
│  │  (ui.md)     │     │  Response    │                         │
│  └──────────────┘     └──────────────┘                         │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 2. Project Configuration

### 2.1 web_app.toml

```toml
[app]
name = "myapp"
env_default = "dev"

# Externalized config (Spring-style)
[config]
files = ["config/app.toml", "config/app.{env}.toml"]
env_prefix = "APP_"

# Directory roles and preludes
[[dir]]
path = "app/controllers"
role = "controller"
prelude = ["simpleweb.http", "simpleweb.routing"]

[[dir]]
path = "app/services"
role = "service"
prelude = ["simpleweb.di", "simpleweb.log"]

[[dir]]
path = "app/ui"
role = "ui"
prelude = ["simpleweb.ui"]

# Starters (auto-config bundles)
[starter]
web = true
json = true
metrics = true
health = true

# Client build
[client]
target = "wasm"
out_dir = "public/assets"
```

### 2.2 Config Layering

Priority (highest to lowest):
1. CLI arguments (`--port=8080`)
2. Environment variables (`APP_PORT=8080`)
3. `config/app.{env}.toml` (environment-specific)
4. `config/app.toml` (defaults)

---

## 3. Routing

### 3.1 Route Definition

Routes are defined in `config/routes.spl`:

```spl
use simpleweb.routing.*

routes:
    # Basic routes
    get  "/"           => HomeController.index
    get  "/about"      => HomeController.about

    # Resource routes (REST)
    resources "users":
        # GET    /users          => UsersController.index
        # GET    /users/:id      => UsersController.show
        # GET    /users/new      => UsersController.new
        # POST   /users          => UsersController.create
        # GET    /users/:id/edit => UsersController.edit
        # PUT    /users/:id      => UsersController.update
        # DELETE /users/:id      => UsersController.destroy

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

### 3.2 Path Parameters

```spl
# Route: GET /users/:id/posts/:post_id
fn show(req):
    let user_id = req.params["id"]
    let post_id = req.params["post_id"]
```

### 3.3 Query Parameters

```spl
# URL: /search?q=hello&page=2
fn search(req):
    let query = req.query["q"] or ""
    let page = req.query["page"].parse_int() or 1
```

---

## 4. Controllers

### 4.1 Page Controller

Returns `.sui` pages (SSR):

```spl
# app/controllers/users_controller.spl

use simpleweb.*

class UsersController:
    @inject
    let user_service: UserService

    fn index(req) -> Response:
        let users = user_service.list_all()
        # Implicit render: app/ui/pages/users/Index.page.sui
        return page({ users: users })

    fn show(req) -> Response:
        let id = req.params["id"].parse_int()?
        let user = user_service.find(id)?
        # Explicit page with props
        return page("users/Show", { user: user })

    fn create(req) -> Response:
        let data = req.body.parse_json()?
        let user = user_service.create(data)?
        return redirect("/users/" + user.id)
```

### 4.2 API Controller

Returns JSON:

```spl
# app/controllers/api/users_controller.spl

use simpleweb.*

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

### 4.3 Response Helpers

```spl
# Page responses (SSR)
page(props)                    # Implicit view from controller/action
page("path/View", props)       # Explicit view
page(props, layout="Admin")    # Custom layout

# JSON responses
json(data)                     # 200 OK
json(data, status=201)         # Custom status
json_error(status, message)    # Error response

# Redirects
redirect(url)                  # 302 Found
redirect(url, permanent=true)  # 301 Moved

# Raw responses
text(content)                  # text/plain
html(content)                  # text/html
file(path)                     # File download
stream(iterator)               # Streaming response
```

---

## 5. Services

### 5.1 Service Definition

```spl
# app/services/user_service.spl

use simpleweb.di.*

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

    fn find(id: i64) -> Option[User]:
        db.query_one("SELECT * FROM users WHERE id = ?", id)

    fn create(data: Dict) -> Result[User, Error]:
        validate_user(data)?
        let user = db.insert("users", data)?
        cache.delete("users:all")
        Ok(user)
```

### 5.2 Dependency Injection

```spl
# Automatic injection via @inject
class MyController:
    @inject
    let user_service: UserService

    @inject
    let logger: Logger

# Manual registration (for interfaces)
# config/services.spl
services:
    bind(Database).to(PostgresDatabase)
    bind(Cache).to(RedisCache)
    bind(Logger).to(FileLogger)
```

---

## 6. Middleware

### 6.1 Defining Middleware

```spl
# app/middleware/auth.spl

use simpleweb.*

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

### 6.2 Applying Middleware

```spl
# config/routes.spl

routes:
    # Global middleware
    use AuthMiddleware
    use LoggingMiddleware

    # Route-specific
    namespace "/admin":
        use AdminAuthMiddleware
        get "/" => AdminController.dashboard
```

---

## 7. Request/Response Objects

### 7.1 Request

```spl
class Request:
    method: str              # GET, POST, PUT, DELETE, etc.
    path: str                # /users/123
    params: Dict[str, str]   # Path params {:id => "123"}
    query: Dict[str, str]    # Query params
    headers: Dict[str, str]  # HTTP headers
    body: Body               # Request body
    context: Dict[str, Any]  # Middleware data

    fn cookie(name: str) -> str?
    fn header(name: str) -> str?
    fn is_json() -> bool
    fn is_ajax() -> bool
```

### 7.2 Response

```spl
class Response:
    status: i32
    headers: Dict[str, str]
    body: Body

    fn set_cookie(name, value, opts)
    fn set_header(name, value)
```

---

## 8. Production Features

### 8.1 Health & Metrics (via Starters)

```toml
# web_app.toml
[starter]
health = true   # Enables /health endpoint
metrics = true  # Enables /metrics endpoint
```

Endpoints:
- `GET /health` - Liveness check
- `GET /health/ready` - Readiness check (DB, cache, etc.)
- `GET /metrics` - Prometheus-format metrics

### 8.2 Custom Health Checks

```spl
# config/health.spl

health_checks:
    check "database":
        db.ping()

    check "cache":
        cache.ping()

    check "external_api":
        http.get("https://api.example.com/health").ok()
```

---

## 9. Auto-Config with Backoff

Starters provide defaults that back off when you define explicit configs:

```spl
# Starter provides default Router
# But if you define your own, starter backs off:

@service
class CustomRouter(Router):
    # Your custom implementation
    # Starter's default Router is NOT used
```

---

## 10. CLI Tools

```bash
# Development
simple web serve              # Start dev server
simple web serve --port=3000  # Custom port

# Routes
simple web routes             # List all routes
simple web explain route GET /users/:id

# Generation
simple web generate controller Users
simple web generate service UserService

# Production
simple web build              # Build for production
simple web start              # Start production server
```

---

## 11. Directory Structure

```
myapp/
  web_app.toml                 # Project config
  config/
    app.toml                   # Default config
    app.dev.toml               # Dev overrides
    app.prod.toml              # Prod overrides
    routes.spl                 # Route definitions
    services.spl               # DI bindings
  app/
    controllers/
      home_controller.spl
      users_controller.spl
      api/
        users_controller.spl
    services/
      user_service.spl
      auth_service.spl
    middleware/
      auth.spl
      logging.spl
    ui/                        # See ui.md
      pages/
      components/
      layouts/
    logic/                     # See ui.md
      pages/
      components/
  public/
    assets/                    # Static files
  test/
    controllers/
    services/
```

---

## 12. Full Example: Blog API + Pages

### 12.1 Routes

```spl
# config/routes.spl

routes:
    # Pages (SSR)
    get "/" => HomeController.index
    resources "posts":
        resources "comments"

    # API
    namespace "/api/v1":
        resources "posts", only=[index, show, create]
```

### 12.2 Controller

```spl
# app/controllers/posts_controller.spl

class PostsController:
    @inject
    let post_service: PostService

    fn index(req) -> Response:
        let posts = post_service.recent(limit=10)
        page({ posts: posts })

    fn show(req) -> Response:
        let id = req.params["id"].parse_int()?
        let post = post_service.find(id)?
        page({ post: post })

    fn create(req) -> Response:
        let user = req.context["user"]
        let data = req.body.parse_form()?
        let post = post_service.create(user, data)?
        redirect("/posts/" + post.id)
```

### 12.3 API Controller

```spl
# app/controllers/api/posts_controller.spl

class PostsController:
    @inject
    let post_service: PostService

    fn index(req) -> Response:
        let page = req.query["page"].parse_int() or 1
        let posts = post_service.paginate(page, per_page=20)
        json({
            posts: posts.items,
            total: posts.total,
            page: page
        })

    fn show(req) -> Response:
        let id = req.params["id"].parse_int()?
        match post_service.find(id):
            Some(post) => json(post)
            None => json_error(404, "Post not found")

    fn create(req) -> Response:
        let data = req.body.parse_json()?
        match post_service.create(req.context["user"], data):
            Ok(post) => json(post, status=201)
            Err(e) => json_error(422, e.message)
```

---

## 13. See Also

- `doc/ui.md` - UI templates, SSR, client components (`.sui` syntax)
- `doc/features/feature.md` - Feature list (#520-536)
- `doc/spec/language.md` - Simple language specification
