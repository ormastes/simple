# Simple Web Server — Architecture Split

> **Related docs:**
> - Lightweight lib API: [`simple_web_server_lib_api.md`](simple_web_server_lib_api.md)
> - Full example design: [`simple_web_server_example.md`](simple_web_server_example.md)
> - Lib source: `src/lib/nogc_sync_mut/http_server/`
> - Example source: `examples/simple_web_server/`

## Overview

Split the web server stack into two tiers:

| Tier | Location | Purpose |
|------|----------|---------|
| **Lightweight Lib** | `src/lib/nogc_sync_mut/http_server/` | Embeddable sync HTTP server for any Simple app |
| **Full Example** | `examples/simple_web_server/` | Standalone feature-rich web server reusing the lib |

The lightweight lib is imported as `use std.nogc_sync_mut.http_server.*` (or `use std.http_server.*` via re-export). The full example demonstrates how to layer middleware, TLS, WebSocket, and static-file serving on top of that core.

## Motivation

Current web server code is scattered across three layers with overlapping responsibilities:

1. **`src/lib/nogc_async_mut/http_server/`** — 25-module async server (router, middleware, CORS, CSRF, compression, rate-limit, security headers, static files, metrics, WebGPU assets, etc.). Full-featured but async-only and heavyweight for simple use cases.
2. **`src/app/ui.web/`** — `WebServer` (sync) and `AsyncWebServer` classes. Tightly coupled to `UISession`, SDN tree parsing, and UI rendering. Not reusable outside the UI stack.
3. **`src/app/io/http_sffi.spl`** — SFFI wrappers around `rt_http_server_*` externs (hyper-based). Provides `HttpServer` with route registration and static-file mount, but requires the Rust runtime extern layer.

**Problem:** There is no minimal, sync, pure-Simple HTTP server that can be embedded into CLI tools, MCP servers, dashboards, or test harnesses without pulling in the async runtime or UI dependencies.

## Boundary Definition

### Lightweight Lib (`src/lib/nogc_sync_mut/http_server/`)

Sync, no GC, minimal surface. Depends only on:
- `std.nogc_sync_mut.net.tcp` (TcpListener, TcpStream)
- `std.common.text` (string utilities)
- `std.common.json` (optional, for JSON responses)

| Module | Responsibility |
|--------|---------------|
| `types.spl` | `HttpRequest`, `HttpResponse`, `HttpMethod`, `HttpStatus` |
| `parser.spl` | Request-line + header + body parsing from `TcpStream` |
| `response.spl` | Response builder and writer (status, headers, body → wire format) |
| `router.spl` | Method + path → handler dispatch (exact match + prefix match) |
| `server.spl` | `SimpleHttpServer` — bind, accept loop, per-connection thread spawn |
| `__init__.spl` | Re-exports public API |

**Not included in lightweight lib:**
- TLS termination
- WebSocket upgrade
- Middleware chain (CORS, CSRF, compression, rate-limit)
- Static-file serving / sendfile
- Auth / session management
- Access logging / metrics
- Async / event-loop patterns

### Full Example (`examples/simple_web_server/`)

Standalone application that demonstrates layering features on top of the lightweight lib:

| File | Feature |
|------|---------|
| `main.spl` | Entry point, CLI arg parsing, server startup |
| `routes.spl` | Application routes (API + pages) |
| `middleware.spl` | CORS, logging, compression wrappers |
| `static_files.spl` | Directory-based static file serving |
| `tls.spl` | TLS termination using `std.nogc_sync_mut.io.tls_sffi` |
| `websocket.spl` | WebSocket upgrade + broadcast |
| `config.spl` | Server configuration (port, TLS paths, static root, etc.) |
| `public/` | Sample static assets (index.html, style.css) |

The example imports:
```
use std.nogc_sync_mut.http_server.{SimpleHttpServer, HttpRequest, HttpResponse, Router}
```

## Relationship to Existing Modules

| Existing Module | Action |
|----------------|--------|
| `src/lib/nogc_async_mut/http_server/` | **Keep as-is.** This is the async full-featured server. The new sync lib is a separate, lighter alternative — not a replacement. |
| `src/lib/gc_async_mut/http_server/` | **Keep as-is.** GC-tier mirror of the async server. |
| `src/app/ui.web/server.spl` | **Future:** Refactor to use lightweight lib for TCP/HTTP plumbing, keep UI-specific routing on top. Not in scope for initial split. |
| `src/app/ui.web/async_server.spl` | **Keep as-is.** Async + WebSocket + UISession coupling stays in app layer. |
| `src/app/web_dashboard/server.spl` | **Future:** Candidate to refactor onto lightweight lib. Dashboard routes stay app-specific. |
| `src/app/io/http_sffi.spl` | **Keep as-is.** SFFI-based server is a different approach (Rust hyper runtime). The new lib is pure-Simple TCP. |

## Design Principles

1. **Pure Simple** — No SFFI externs beyond `TcpListener`/`TcpStream` (already in `nogc_sync_mut`).
2. **Sync-first** — One thread per connection. Simple to understand, debug, embed.
3. **Composable** — Router accepts `fn(HttpRequest) -> HttpResponse` handlers. Middleware is just handler wrapping.
4. **Zero mandatory dependencies** — No JSON, no TLS, no file-system unless the caller brings them.
5. **Embeddable** — Instantiate `SimpleHttpServer`, add routes, call `start()`. Three lines to a working server.

## Migration Path

1. **Phase 1 (this design):** Create lightweight lib + full example. No changes to existing code.
2. **Phase 2 (future):** Refactor `src/app/ui.web/server.spl` to delegate TCP/HTTP parsing to the lib.
3. **Phase 3 (future):** Refactor `src/app/web_dashboard/server.spl` similarly.
4. **Phase 4 (future):** Evaluate whether `nogc_async_mut/http_server/` should share types with the sync lib.
