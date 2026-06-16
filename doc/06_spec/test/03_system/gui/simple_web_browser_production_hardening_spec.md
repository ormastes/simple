# Simple Web Browser Production Hardening Spec

Generated/manual scenario mirror for
`test/03_system/gui/simple_web_browser_production_hardening_spec.spl`.

## Scenario: fails closed on unauthenticated browser HTTP and WebSocket routes

1. Start the test-only launcher
   `test/03_system/gui/ui_browser/simple_web_hardening_server.spl`, which calls
   the production `app.ui.web.server.run_web` entrypoint against
   `test/03_system/gui/ui_browser/fixtures/hello.ui.sdn` with a deterministic
   test token secret, then wait until the socket accepts connections.
2. Send a raw `POST /ui/login` request without an `Origin` header.
3. Send a raw `POST /ui/login` request with `Content-Length: 8193` and no body,
   proving the server rejects oversized unauthenticated requests before reading
   the body.
4. Send a raw `GET /api/state` request with an allowed loopback origin but no
   bearer token.
5. Send a raw WebSocket upgrade request for `/ui/ws` with an allowed loopback
   origin but no bearer token.
6. Stop the subprocess.

Expected evidence:

- Missing-origin login returns `HTTP/1.1 403` with `forbidden_origin`.
- Oversized unauthenticated login returns `HTTP/1.1 413` with
  `request_body_too_large`.
- Unauthenticated `/api/state` returns `HTTP/1.1 403`.
- Unauthenticated `/ui/ws` upgrade returns `HTTP/1.1 403` instead of `101`.
