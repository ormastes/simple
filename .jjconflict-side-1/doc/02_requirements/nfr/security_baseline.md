# NFR – Security Baseline

**Related requirements:** [doc/02_requirements/feature/security_aop.md](../requirement/security_aop.md), [doc/02_requirements/feature/simple_tauri.md](../requirement/simple_tauri.md)
**Related research:** [doc/01_research/security_aop_architecture_2026-03-28.md](../../research/security_aop_architecture_2026-03-28.md)
**Related design:** [doc/05_design/security_aop.md](../../design/security_aop.md)

## Performance

- Security middleware overhead < 1ms P95 per request
- CSRF token generation < 0.5ms P95
- Input sanitization < 0.1ms P95 for typical payloads (< 64KB)
- Capability policy check < 0.01ms (hash lookup)
- Rate limit check < 0.05ms (token bucket update)

## Reliability

- Zero false-positive CSRF rejections on valid requests
- Capability checks must never panic — always return Result
- Rate limiter must not leak memory under sustained load
- Audit log failures must not crash the application (degrade gracefully)
- Security headers middleware must not corrupt response bodies

## Security

- CSRF tokens use HMAC-SHA256 via existing `crypto_ffi.spl`
- Session tokens expire within 30 minutes (configurable)
- No secrets in audit logs (mask tokens, keys, passwords)
- CSP headers on all HTML responses: `default-src 'self'; script-src 'self'; style-src 'self' 'unsafe-inline'`
- X-Content-Type-Options: nosniff on all responses
- X-Frame-Options: DENY on all responses
- Strict-Transport-Security: max-age=31536000; includeSubDomains
- Referrer-Policy: strict-origin-when-cross-origin
- Input sanitization on all user-provided content rendered to HTML
- URL sanitization rejects `javascript:`, `data:`, `vbscript:` schemes
- Path traversal prevention: reject `../`, null bytes, encoded variants
- UI capability enforcement: default-deny per window
- IPC message validation: length limits, type checks, sanitization

## Observability

- All security events emit structured JSON audit log entries
- Each entry includes: timestamp_ms, event type, correlation_id, module_path
- Failed auth attempts logged with peer_addr
- Capability denials logged with window_id and requested capability
- Rate limit hits logged with peer_addr and path
- Audit log supports file output (append mode)

## Compatibility

- All security modules in `.spl` — no new FFI dependencies
- Reuses existing `crypto_ffi.spl` (ring, argon2 bindings)
- Works across all supported platforms (Linux x86_64, arm64, Windows, macOS)
- MDSOC security dimension compatible with existing capsule system

## Verification

| NFR | Test / Tool | Threshold |
|-----|-------------|-----------|
| Middleware P95 latency | Load test (1000 req) | < 1ms |
| CSRF correctness | Unit tests + fuzz | 0 false positives |
| Sanitization bypass | Fuzz test (sanitize_fuzz) | 0 bypasses |
| Capability enforcement | Unit tests (policy_spec) | 100% deny on ungranteds |
| Audit log format | Unit tests | Valid JSON per entry |
| AOP weaving correctness | Weaving spec tests | All join points matched |
| Layer violation | MDSOC layer checker | 0 violations |
| Memory safety | Rate limiter stress test | No leaks after 100K req |
