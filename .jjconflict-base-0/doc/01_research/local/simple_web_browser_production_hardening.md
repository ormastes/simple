# Simple Web Browser Production Hardening Local Research

## Scope

This lane covers production hardening for the Simple Web browser boundary:
token secret policy, Origin enforcement, WebSocket authentication, sensitive
API route protection, generated browser client behavior, and renderer parity
evidence gates.

## Current Implementation Surface

- `src/app/ui.web/session_token.spl` signs and verifies origin-bound bearer
  tokens and now fails closed on missing production secrets unless explicit
  non-TLS local development fallback is enabled.
- `src/app/ui.web/origin_guard.spl` rejects missing/disallowed Origin headers
  and limits the default local-development policy to loopback HTTP/HTTPS
  origins with optional numeric ports.
- `src/app/ui.web/auth_params.spl` centralizes auth-path bearer extraction,
  query parsing, and single-pass percent decoding.
- `src/app/ui.web/ws_handler.spl` and `src/app/ui.web/ui_routes.spl` gate
  WebSocket upgrades with origin and token verification before handshakes.
- `src/app/ui.web/server.spl`, `tls_serve_loop.spl`, and `async_server.spl`
  gate `/api/state`, `/api/widgets`, and `/api/clients` with the shared
  authorization helper.
- `src/app/ui.web/html.spl` generated browser clients authenticate through
  `/ui/login` and now send WebSocket bearer tokens through
  `Sec-WebSocket-Protocol` instead of URL query strings.

## Current Evidence

- `test/01_unit/app/ui/web_auth_hardening_spec.spl` covers secret fallback,
  Origin fail-closed behavior, default loopback policy, explicit allowlist
  parsing, sensitive API auth status, generated browser client auth, and
  one-pass query token decoding.
- `test/01_unit/app/ui/ws_handler_spec.spl` covers WebSocket upgrade parsing,
  handshake accept generation, Authorization/query/subprotocol bearer
  extraction, response subprotocol selection, and precedence.
- `scripts/check/check-production-gui-web-renderer-parity-evidence.shs` was
  run in this lane. The generated GUI matrix passed, but the wrapper failed at
  the layout manifest gate with `electron-layout-manifest-failed`.

## Gaps

- Final feature and NFR requirements for this lane are not selected yet.
- System-level live endpoint coverage is still missing for `/ui/login`,
  `/ui/ws`, `/ws`, `/ui/resume`, and oversized unauthenticated request bodies.
- Login/token vending has no rate or burst control.
- Query-token acceptance remains as a compatibility fallback and should be
  retired or explicitly restricted after live clients are migrated.
- Full renderer parity is not achieved: the layout manifest currently reports
  16 exact failures and 2 tracked divergences.
