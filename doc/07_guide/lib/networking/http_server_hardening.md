# HTTP Server Hardening — Shared Protocol Core

Both HTTP server transports enforce one hardening policy, implemented once in
`src/lib/common/net/http_core.spl` (`std.common.net.http_core`):

- `nogc_sync_mut/http_server` — blocking, thread-per-connection (chunked
  Transfer-Encoding fails closed with 501).
- `nogc_async_mut/http_server` — event-driven workers (chunked supported,
  decoded through the core's bounded decoder).

## What the core owns

| Concern | Function | Violation |
|---------|----------|-----------|
| Request-line length (8192 default) | limit constants + parser wiring | 431 |
| Header count (100) / header line (8192) | limit constants + parser wiring | 431 |
| Content-Length validity, duplicates, size | `body_decision(headers, max_body, allow_chunked)` | 400 / 413 |
| Chunked policy (incl. CL+TE smuggling ambiguity) | `body_decision` | 400 / 501 |
| Bounded chunked decoding | `decode_chunked_bounded(raw, max_body)` | 400 / 413 |
| Path traversal (`..`, `%2e%2e`, `//`, `\`, `%00`) | `path_is_safe(path)` | 400 |
| Route pattern matching (`:param`, `*`) | `match_route_pattern` / `extract_route_params` | — |

Key invariant on the async transport: limits fire DURING parsing, before
buffer growth — an endless request line or streamed oversized body is cut off
while incomplete, not after it has been buffered.

## Wiring map

- Sync parser `parse_request_with_limits` and router `dispatch` delegate to
  the core (`export use` keeps the historical import paths working).
- Async `HttpRequestParser.new()` uses the shared defaults;
  `HttpRequestParser.with_limits(...)` overrides per server.
- Async `AsyncRouter.route` rejects unsafe paths BEFORE location matching;
  the worker maps that to a 400 and re-checks the path in its inline static
  handler before `root + path` concatenation (defence in depth).
- Async worker dispatch: `handler_type == "static"`/`""` uses the inline
  static fast path; anything else dispatches through `HandlerRegistry` under
  a server-established task security context
  (`dispatch_with_task_remote_security_context`) — client permission headers
  are never authority.

## Deployment rule

Until direct TLS/HTTP2 hardening completes, terminate TLS/H2 at a mature edge
proxy and expose these servers on private HTTP/1.1 only. See the assessment:
`doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md` §3.

## Specs (evidence)

- `test/01_unit/lib/common/net/http_core_spec.spl` — core policy corpus.
- `test/01_unit/lib/http_server/{parser_limits,path_safety,chunked_rejection}_spec.spl` — sync transport.
- `test/01_unit/lib/nogc_async_mut/http_server/async_{parser_limits,path_safety,dynamic_dispatch}_spec.spl` — async transport.
- `test/03_system/app/enterprise/store_web_harden_spec.spl` — the store web
  app consuming this core live: unauthenticated denial, HTML escaping, shared
  security headers, http_core limit/traversal gating (manual:
  `doc/06_spec/store_web_harden_spec.md`).

Known gaps (tracked in `.spipe/simple_enterprise_suite/state.md`): the
tier-copied `std.http.{limits,path_security}` modules overlap this policy and
should be unified onto the core; a live-socket system spec for dynamic
dispatch is still pending.
