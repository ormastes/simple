# SimpleWeb Framework Guide

Rails-like web application framework built on the async HTTP server. Convention-over-configuration with MDSOC security, embedded SQLite, template SSR, and client-side progressive enhancement.

---

## Architecture

```
WebApp (app.sdn config)
  |
  +-- WebRouter (routes.sdn)
  |     |
  |     +-- AppDispatcher (registers as "app" handler in HandlerRegistry)
  |           |
  |           +-- ControllerContext (request, session, flash, params)
  |                 |
  |                 +-- render_page() -> Template SSR
  |                 +-- render_json() -> JSON API
  |                 +-- render_redirect() -> 302
  |
  +-- HttpServer (nginx-style async, N workers, SO_REUSEPORT)
  +-- SessionStore (DB-backed or cookie-signed)
  +-- Database (SQLite with migrations)
  +-- MiddlewarePipeline (phase-based: PostAccept -> Access -> Content -> Log)
  +-- AOP Security (default-deny, compile-time weaving)
```

---

## Quick Start

```simple
# main.spl
use std.web_framework.app.{WebApp}

fn main():
    val app = WebApp.new("app.sdn")?
    app.mount_routes("routes.sdn")?
    app.start()?
    app.wait()
```

### Configuration (app.sdn)

```sdn
app:
  name: "my-app"
  env: "development"
  secret_key: "${MY_SECRET_KEY}"

server:
  listen: "0.0.0.0:3000"
  worker_count: 0

database:
  path: "app.db"

session:
  store: "database"
  ttl_seconds: 86400
  cookie_name: "_session"

assets:
  path: "public"
  fingerprint: false
```

---

## Routing

Routes defined in `routes.sdn`:

```sdn
routes:
  - method: GET
    path: "/"
    controller: HomeController
    action: index
    auth: public

  - method: GET
    path: "/users/:id"
    controller: UsersController
    action: show

  - method: POST
    path: "/users"
    controller: UsersController
    action: create

  # API namespace
  - method: GET
    path: "/api/v1/packages"
    controller: Api.PackagesController
    action: index
    auth: public
```

Or programmatically:

```simple
use std.web_framework.router.{WebRouter}

var router = WebRouter.new()
router.get("/", "HomeController", "index")
router.resources("users")  # generates 7 RESTful routes
router.namespace("/api/v1", api_routes)
```

### RESTful Resources

`router.resources("users")` generates:

| Method | Path | Action |
|--------|------|--------|
| GET | /users | index |
| GET | /users/new | new_form |
| POST | /users | create |
| GET | /users/:id | show |
| GET | /users/:id/edit | edit |
| PUT | /users/:id | update |
| DELETE | /users/:id | destroy |

---

## Controllers

Controllers use **composition** (no inheritance). Each action receives a `ControllerContext`:

```simple
use std.web_framework.controller.{ControllerContext, render_page, render_json, render_redirect, render_error}
use std.web_framework.view_model.{ViewData}

@public
fn action_index(ctx: ControllerContext) -> HttpResponseData:
    val data = ViewData.new()
        .set("title", "Welcome")
        .set("message", "Hello, world!")
    render_page(ctx, "home/index", data.to_dict())

@requires_auth
fn action_show(ctx: ControllerContext) -> HttpResponseData:
    val id = ctx.params.get("id") ?? "0"
    val user = find_user(id)?
    match user:
        Some(u):
            val data = ViewData.new().set("user_name", u.username)
            render_page(ctx, "users/show", data.to_dict())
        nil:
            render_error(404, "User not found")
```

### Response Helpers

```simple
render_page(ctx, "view/path", data)  # Template SSR (auto-escapes)
render_json(json_string)             # application/json
render_redirect("/path")             # 302 redirect
render_text("content")               # text/plain
render_html("<h1>Raw</h1>")          # text/html
render_error(404, "Not found")       # Error page
```

### ControllerContext

```simple
class ControllerContext:
    request: HttpRequestData        # method, path, headers, body, peer_addr
    session_data: Dict<text, text>  # current session
    flash_messages: [FlashMessage]  # flash from previous request
    params: Dict<text, text>        # merged route + query + body params
    current_user_id: text?          # set by auth middleware
```

---

## Models (ActiveModel)

Thin Active Record wrapper over `Repository<T>` + `DbCodec<T>`:

```simple
use std.database.sql.types.{DbValue, DbRow}
use std.database.sql.codec.{DbCodec}
use std.web_framework.model.{ActiveModel}

class Todo:
    id: i64
    title: text
    completed: bool
    user_id: i64

class TodoCodec:
    fn table_name() -> text: "todos"
    fn columns() -> [text]: ["title", "completed", "user_id"]
    fn encode(todo: Todo) -> [DbValue]:
        [DbValue.Text(todo.title), DbValue.Integer(if todo.completed: 1 else: 0), DbValue.Integer(todo.user_id)]
    fn decode(row: DbRow) -> Todo:
        Todo(id: row.get_int("id"), title: row.get_text("title"), ...)
    fn schema() -> TableSchema: ...

# Usage
var model = ActiveModel.new(repo)
model.validates_presence("title")
val id = model.save(todo)?
val todos = model.paginate(1, 10)?
```

### Database Migrations

```simple
use std.database.sql.migration.{MigrationRunner, Migration}

fn run_migrations(db: Database):
    var runner = MigrationRunner.new(db)
    runner.add(Migration(
        name: "001_create_todos",
        up: "CREATE TABLE todos (id INTEGER PRIMARY KEY AUTOINCREMENT, title TEXT NOT NULL, completed INTEGER DEFAULT 0, user_id INTEGER, created_at TEXT)",
        down: "DROP TABLE todos"
    ))
    runner.run_pending()?
```

---

## Templates

Handlebars-like engine with auto-escaping:

```html
{{#layout "application"}}

<h1>{{title}}</h1>

{{#if logged_in}}
  <p>Welcome, {{username}}!</p>
{{else}}
  <a href="/login">Login</a>
{{/if}}

{{#each todos}}
  <div class="todo">
    <span>{{this}}</span>
  </div>
{{/each}}

{{>_pagination}}

{{/layout}}
```

### Features
- `{{var}}` -- auto-escaped output
- `{{{var}}}` -- raw output (requires `@allow(raw_html)`)
- `{{#if cond}}...{{else}}...{{/if}}` -- conditionals
- `{{#each items}}...{{/each}}` -- loops (`{{this}}`, `{{@index}}`, `{{@first}}`, `{{@last}}`)
- `{{>partial_name}}` -- partials
- `{{#layout "name"}}...{{/layout}}` -- layout wrapping (layout uses `{{{body}}}`)
- Filters: `{{name | upper}}`, `{{name | truncate:20}}`, `{{price | number_format}}`

### Layout Example

```html
<!-- views/layouts/application.html -->
<!DOCTYPE html>
<html>
<head><title>{{title}} - MyApp</title></head>
<body>
  {{>_nav}}
  {{>_flash}}
  <main>{{{body}}}</main>
</body>
</html>
```

---

## Security (Default-Deny)

The framework uses AOP-based security weaved at compile time. **Unannotated handlers default to `@requires_auth`** (fail-closed).

### Annotations

```simple
@public                          # No auth required (opt-in openness)
@requires_auth                   # Must be authenticated (default)
@requires_capability("admin")   # Must hold specific capability
@deny_all                        # Unconditional reject (maintenance mode)
```

### CSRF Protection

```simple
use std.web_framework.csrf_integration.{csrf_hidden_field, csrf_token_for_session}

# In controller: generate token
val token = csrf_token_for_session(session_id, secret)

# In template:
# <form method="POST">
#   {{{csrf_field}}}
#   ...
# </form>
```

### IDOR Prevention

Always verify resource ownership:

```simple
fn action_edit(ctx: ControllerContext) -> HttpResponseData:
    val todo_id = ctx.params.get("id")
    val todo = find_todo(todo_id)?
    if todo.user_id != ctx.current_user_id:
        return render_error(403, "Forbidden")
    render_page(ctx, "todos/edit", ...)
```

---

## Sessions

```simple
use std.web_framework.session.{SessionStore, SignedCookieSession}

# DB-backed sessions
var store = SessionStore.new(db)
val session_id = store.create("user123")
store.set(session_id, "role", "admin")
val data = store.get(session_id)?
store.destroy(session_id)

# Cookie-signed sessions (client-side storage)
val cookie = SignedCookieSession.encode(data, secret)
val data = SignedCookieSession.decode(cookie, secret)?
```

## Flash Messages

```simple
use std.web_framework.flash.{flash_add, flash_get, FlashType}

# Set flash
session = flash_add(session, FlashType.Success, "Todo created!")

# Read in next request (auto-cleared)
val messages = flash_get(session)
```

## Form Validation

```simple
use std.web_framework.form_validation.{Validator, ValidationRule}

var v = Validator.new()
v.add_rule("title", ValidationRule.Required)
v.add_rule("title", ValidationRule.MinLength(1))
v.add_rule("email", ValidationRule.Email)

if not v.validate(ctx.params):
    val errors = v.all_errors()
    # re-render form with errors
```

## Strong Params

```simple
use std.web_framework.params.{StrongParams}

val permitted = StrongParams.permit(["title", "description"])
val safe_params = permitted.filter(ctx.params)
# Only title and description pass through
```

## Pagination

```simple
use std.web_framework.pagination.{Paginator}

val total = repo.count()?
val pager = Paginator.new(page: 1, per_page: 10, total: total)
val offset = pager.offset()  # 0
val pages = pager.total_pages()  # 5
```

---

## Auth Middleware

```simple
use std.web_framework.auth_middleware.{session_auth_middleware, jwt_auth_middleware}

# Session-based (web pages)
val user_id = session_auth_middleware(request, session_store)?

# JWT-based (API)
val user_id = jwt_auth_middleware(request, jwt_secret)?
```

---

## Asset Pipeline

```simple
use std.web_framework.asset_pipeline.{AssetPipeline}

var pipeline = AssetPipeline.new("public", fingerprint: true)
pipeline.build()?
val url = pipeline.asset_path("css/app.css")
# -> "/css/app-a1b2c3d4.css" (fingerprinted)
```

---

## Client-Side Support

### Live Reload (Development)

```simple
use std.web_framework.live_reload.{LiveReloadServer, live_reload_script}

# Inject in dev mode:
val script = live_reload_script(35729)
```

### SimpleFetch (CSRF-aware)

The framework generates `simple-framework.js` with:
- `SimpleFetch.get/post/put/delete()` -- auto-injects CSRF token
- `SimpleWS` -- WebSocket with auto-reconnect
- `SimpleHydration` -- progressive enhancement via `data-spl-*` attributes

---

## Project Structure

```
myapp/
    main.spl                 # Entry point
    app.sdn                  # Configuration
    routes.sdn               # Route definitions
    db/
        migrations.spl       # Database schema
    controllers/
        home_controller.spl
        users_controller.spl
    models/
        user.spl
    services/
        auth_service.spl
    views/
        layouts/
            application.html # Main layout
        home/
            index.html
        shared/
            _nav.html        # Navigation partial
            _flash.html      # Flash messages
    public/
        css/style.css
        js/app.js
    .env.example             # Required env vars (no values)
    .gitignore
```

---

## Module Reference

| Module | Location | Purpose |
|--------|----------|---------|
| `std.web_framework.app` | `nogc_async_mut/web_framework/app.spl` | WebApp entry point |
| `std.web_framework.router` | `nogc_async_mut/web_framework/router.spl` | Convention-based router |
| `std.web_framework.dispatcher` | `nogc_async_mut/web_framework/dispatcher.spl` | Controller dispatch |
| `std.web_framework.controller` | `common/web_framework/controller.spl` | ControllerContext, response helpers |
| `std.web_framework.model` | `nogc_sync_mut/web_framework/model.spl` | ActiveModel<T> |
| `std.web_framework.session` | `nogc_sync_mut/web_framework/session.spl` | Session stores |
| `std.web_framework.form_validation` | `common/web_framework/form_validation.spl` | Validator |
| `std.web_framework.form_parser` | `nogc_sync_mut/web_framework/form_parser.spl` | Body parsing |
| `std.web_framework.flash` | `common/web_framework/flash.spl` | Flash messages |
| `std.web_framework.params` | `common/web_framework/params.spl` | StrongParams |
| `std.web_framework.pagination` | `common/web_framework/pagination.spl` | Paginator |
| `std.web_framework.auth_middleware` | `nogc_sync_mut/web_framework/auth_middleware.spl` | Session + JWT auth |
| `std.web_framework.csrf_integration` | `nogc_sync_mut/web_framework/csrf_integration.spl` | CSRF protection |
| `std.web_framework.asset_pipeline` | `nogc_sync_mut/web_framework/asset_pipeline.spl` | Asset fingerprinting |
| `std.web_framework.live_reload` | `nogc_async_mut/web_framework/live_reload.spl` | Dev live reload |
| `std.web_framework.client_hydration` | `common/web_framework/client_hydration.spl` | Progressive enhancement |

---

## Security Lint Rules

The compiler includes 6 security lint rules (activated by `bin/simple build lint`):

| Rule | Code | Level | Detects |
|------|------|-------|---------|
| SQL Injection | SEC-SQL001 | deny | String interpolation with SQL keywords |
| Hardcoded Secret | SEC-SEC001-008 | deny | API keys, tokens, private keys |
| Insecure Comparison | SEC-CMP001 | warn | `==` on password/token vars |
| Raw HTML | SEC-XSS001-003 | warn | Unescaped HTML output |
| Missing Auth | SEC-AUTH001 | warn | Handler without security annotation |
| SSRF | SEC-SSRF001-002 | warn | User input in URL fetch |

---

## Example Application

See `examples/webapp/` for a complete todo-list application demonstrating all features.

## Related

- Security guide: `doc/07_guide/security/webapp_security.md`
- Secret prevention: `doc/07_guide/security/secret_prevention.md`
- LLM security research: `doc/01_research/local/llm_webapp_security_holes.md`
- Portal server: `src/app/portal/`
- HTTP server internals: `src/lib/nogc_async_mut/http_server/`
- Template engine: `src/lib/common/template/`
- Database: `src/lib/nogc_sync_mut/database/sql/`
