# Secure Pure-Simple production web server

Source: `test/03_system/web/server/secure_pure_simple_web_server_spec.spl`

## Primary operator flow

1. **Bind the production listener.** Construct `SecureServerPolicy.production`,
   validate every bound, and confirm plaintext development mode is disabled.
2. **Reject an unsafe web request before dispatch.** Reject encoded traversal,
   ambiguous `Content-Length`, every unsupported transfer coding, and duplicate
   singleton security headers before the router can invoke application code.
   The native line API's 4096-byte truncation boundary is explicit evidence.
3. Start TLS only with present, structurally valid certificate and private-key
   material. Missing or invalid material is a startup error. Plaintext requires
   an explicit capability passed to both `SecureServerPolicy.plaintext_dev`
   and `start_plaintext`.
4. Attach the socket peer address to the request before routing and apply
   default CSP, nosniff, frame-denial, and referrer headers before writing.
5. A TLS accept failure owns and closes its TCP stream. GAP-TLS-3 remains the
   exact blocker to encrypted application traffic; no plaintext fallback is
   accepted as production evidence. A failed connection with empty ALPN is
   classified as neither HTTP/1 nor HTTP/2.
6. A shared atomic admission owner claims before thread spawn. Exactly the
   configured connection boundary is admitted; boundary+1 closes before thread
   spawn, while every admitted handler releases its slot
   on completion.

## Absolute oracles

- Production policy validation returns the empty error string and retains one
  request per connection with finite read/write bounds.
- Unsafe traversal is `false`; malformed framing returns its exact rejection
  category; invalid TLS material returns a non-empty error.
- No executable spec is stored under `doc/06_spec`; this manual has 0 stubs.
- Plaintext startup requires both an explicit development policy and a
  non-empty `PlaintextDevelopmentCapability` audit reason.
- The default production `start()` returns an error and never silently opens a
  plaintext listener; loopback callers handle their typed startup result.
- A two-slot admission fixture accepts two, rejects the third, releases to one,
  and accepts a replacement through the same shared atomic handle.
