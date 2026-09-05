# Simple Web Browser Production Hardening Architecture

## Status

Implementation-aligned architecture note for the selected Feature Option C and
NFR Option C scope recorded in
`doc/02_requirements/feature/simple_web_browser_production_hardening.md` and
`doc/02_requirements/nfr/simple_web_browser_production_hardening.md`.

## Boundary

The production browser boundary is the Simple Web HTTP/WebSocket entrypoint:

- Plain HTTP server: `src/app/ui.web/server.spl`
- TLS server loop: `src/app/ui.web/tls_serve_loop.spl`
- Async server: `src/app/ui.web/async_server.spl`
- Shared `/ui/*` dispatch: `src/app/ui.web/ui_routes.spl`
- Token and origin policy: `src/app/ui.web/session_token.spl`,
  `src/app/ui.web/origin_guard.spl`, `src/app/ui.web/auth_params.spl`
- Browser clients: generated JS in `src/app/ui.web/html.spl` and static WM
  client `src/app/ui.web/wm.js`

The boundary is fail-closed by default: missing production secrets, missing or
disallowed origins, malformed tokens, wrong-origin tokens, and unauthenticated
sensitive API routes must fail before state data, snapshots, or WebSocket
upgrade success are returned.

## Auth Model

`SIMPLE_UI_WEB_TOKEN_SECRET` is the signing root. Non-TLS local development may
opt into an insecure fallback only with `SIMPLE_UI_WEB_ALLOW_INSECURE_DEV_SECRET=1`.
TLS mode never accepts the insecure fallback.

`/ui/login` accepts only allowed origins and bounded unauthenticated bodies. It
issues an HMAC-signed `SessionToken` bound to the request origin. `/ui/ws`,
`/ui/resume`, and sensitive `/api/*` routes require an allowed origin plus a
token verified against that exact origin. Legacy `/ws` is hidden before upgrade
routing and returns `404`.

Browser WebSocket clients authenticate through
`Sec-WebSocket-Protocol: simple-ui, bearer.<url-encoded-token>`. Query-string
bearer transport is deprecated and non-authorizing, including when the legacy
`SIMPLE_UI_WEB_ALLOW_QUERY_TOKEN=1` environment knob is present.

## Renderer Evidence Gate

The release evidence gate is
`scripts/check/check-production-gui-web-renderer-parity-evidence.shs`. It must
record marker-free, exact renderer parity for the current GUI/Web slice:

- generated GUI/Web matrix pass
- Electron layout manifest pass
- Tauri/Chrome surface manifest pass with zero fail count
- backend-executed parity pass with no blur/tolerance fallback
- Metal unavailable on Linux only as `metal-requires-macos`

Linux Metal, AMD ROCm, Windows DirectX, and browser WebGPU proof remain
environment-bound follow-ups, documented in
`doc/03_plan/sys_test/simple_web_browser_gpu_environment_matrix.md`.

## Hot Paths

Hot request paths avoid full-tree scans and shell-outs. Authorization uses
header/path/body parsing in-process and performs bounded body reads before
unauthenticated login parsing. Renderer parity wrappers are verification tools,
not request handlers.

## Startup And Invalidation

Startup reads secret/origin environment once per server instance. File-backed UI
content still uses the existing file-change watcher in `server.spl`; auth
configuration changes require server restart.

## Targets

- Missing production secret: startup failure unless explicit non-TLS dev opt-in.
- Unauthorized `/api/*`, `/ui/ws`, `/ui/resume`: `403` before data or upgrade.
- Legacy `/ws`: `404` before upgrade.
- Oversized unauthenticated `/ui/login`: `413`.
- Renderer parity wrapper: exit `0`, `blur_or_tolerance_used=false`, surface
  fail counts `0`.
- Generated-spec layout guard: `find doc/06_spec -name '*_spec.spl' | wc -l`
  returns `0`.
