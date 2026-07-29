# Simple Web Browser Production Hardening Design

## Status

Implementation-aligned detail design for selected Feature Option C and NFR
Option C trace IDs.

## Configuration

- `SIMPLE_UI_WEB_TOKEN_SECRET`: required signing secret.
- `SIMPLE_UI_WEB_ALLOW_INSECURE_DEV_SECRET`: permits local non-TLS fallback only
  when set to `1` or `true`.
- `SIMPLE_UI_WEB_ALLOWED_ORIGINS`: comma-separated exact origins. When unset,
  the development default accepts only loopback HTTP/HTTPS origins with numeric
  ports.
- `SIMPLE_UI_WEB_ALLOW_QUERY_TOKEN`: deprecated compatibility knob; query
  `?token=` bearer extraction is non-authorizing.

## Request Flow

1. Server startup loads `OriginGuard` and token secret, then creates one
   cryptographically random 256-bit login grant plus a distinct random 256-bit
   token grant claim.
2. Root HTML publishes the lowercase-hex grant in the
   `simple-ui-login-grant` same-origin meta tag.
3. `/ui/login` checks origin before reading or parsing the grant body.
4. Content-Length above `UI_WEB_MAX_UNAUTH_BODY_BYTES` returns `413`.
5. Login attempts pass through the existing fixed-window burst gate.
6. Login body fields are parsed through bounded `ui_web_auth_json_field`; a
   missing or non-exact grant returns `403` without a token.
7. Successful login signs the token with the distinct server-owned token grant
   claim and binds it to the accepted origin. The serialized claim cannot be
   replayed as login proof.
8. `/ui/ws`, `/ui/resume`, and sensitive `/api/*` call
   `ui_web_request_authorized`; legacy `/ws` is hidden with `404`.
9. WebSocket upgrade is computed only after origin and token verification pass.

## Token Transport

Generated browser clients and static `wm.js` use the WebSocket subprotocol list:

```text
simple-ui, bearer.<url-encoded-token>
```

The server echoes only `simple-ui`, never the bearer-bearing subprotocol.
Non-browser clients may use `Authorization: Bearer <token>`. Query transport is
deprecated and non-authorizing, including when
`SIMPLE_UI_WEB_ALLOW_QUERY_TOKEN=1` is present.

## Error Contract

- Missing/disallowed origin: `403`.
- Missing/invalid bearer on protected routes: `403`.
- Missing or mismatched login grant: `403`, with no token.
- Oversized unauthenticated login: `413`.
- Unknown `/ui/*`: `404`.

## Evidence

Primary executable evidence:

- `test/01_unit/app/ui/web_auth_hardening_spec.spl`
- `test/01_unit/app/ui/ws_handler_spec.spl`
- `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`
- `scripts/check/check-production-gui-web-renderer-parity-evidence.shs`

Manual/spec evidence:

- `doc/06_spec/03_system/gui/simple_web_browser_production_hardening_spec.md`
- `doc/09_report/production_gui_web_renderer_parity_evidence_2026-06-16.md`
- `doc/09_report/simple_web_browser_production_hardening.md`

## Remaining Design Gaps

- Native macOS Metal and AMD ROCm proof require matching host environments.
