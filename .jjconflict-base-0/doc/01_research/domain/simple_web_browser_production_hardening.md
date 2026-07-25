# Simple Web Browser Production Hardening Domain Research

## Sources

- OWASP Cross-Site Request Forgery Prevention Cheat Sheet:
  `https://cheatsheetseries.owasp.org/cheatsheets/Cross-Site_Request_Forgery_Prevention_Cheat_Sheet.html`
- OWASP WebSocket Security Cheat Sheet:
  `https://cheatsheetseries.owasp.org/cheatsheets/WebSocket_Security_Cheat_Sheet.html`
- MDN Origin header:
  `https://developer.mozilla.org/en-US/docs/Web/HTTP/Reference/Headers/Origin`

## Findings

- Browser state-changing endpoints should validate the request Origin and fail
  closed when the origin is absent or outside the configured trust boundary.
- WebSocket handshakes need the same trust decision as HTTP endpoints because
  browsers can initiate cross-origin WebSocket connections.
- WebSocket authentication should happen before the upgrade is accepted.
- Bearer tokens in URLs are weaker than header-like channels because URLs are
  commonly retained in browser history, intermediary logs, referrers, crash
  reports, and diagnostics.
- CSRF and browser-origin defenses are strongest when Origin checks, explicit
  tokens, and narrow allowed-origin configuration are combined.
- Production defaults should be conservative; local development exceptions
  should require explicit opt-in and should not apply to TLS serving.

## Implications For Simple Web

- `/ui/login` must require an allowed Origin before minting a token.
- `/ui/ws`, `/ws`, `/ui/resume`, and sensitive `/api/*` routes must require an
  allowed Origin and an origin-bound bearer token.
- Generated browser clients should avoid putting bearer tokens in WebSocket
  URLs; `Sec-WebSocket-Protocol` is a practical browser-compatible channel.
- Query-token compatibility should remain temporary and explicit.
- Live endpoint tests should exercise real HTTP/WebSocket behavior, not only
  source-level helper behavior.
