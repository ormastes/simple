# Secure Pure-Simple production web server

Source: `test/03_system/web/server/secure_pure_simple_web_server_spec.spl`

## Primary operator flow

1. **Bind the production listener.** Construct `SecureServerPolicy.production`,
   validate every bound, and confirm plaintext development mode is disabled.
2. **Reject an unsafe web request before dispatch.** Reject encoded traversal,
   ambiguous `Content-Length`, every unsupported transfer coding, and duplicate
   singleton security headers before the router can invoke application code.
3. Start TLS only with present, structurally valid certificate and private-key
   material. Missing or invalid material is a startup error. Plaintext requires
   the explicit `SecureServerPolicy.plaintext_dev()` configuration.

## Absolute oracles

- Production policy validation returns the empty error string and retains one
  request per connection with finite read/write bounds.
- Unsafe traversal is `false`; malformed framing returns its exact rejection
  category; invalid TLS material returns a non-empty error.
- No executable spec is stored under `doc/06_spec`; this manual has 0 stubs.
