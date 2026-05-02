# Security AOP Architecture — Known Limitations

**Feature:** MDSOC/AOP Security Dimension for UI and Web Server
**Date:** 2026-03-28

## Limitations

### L-1: Rate Limiter State Not Persistent

**Description:** `RateLimitStore` uses in-memory parallel arrays. State is lost on process restart.
**Workaround:** Acceptable for single-process servers. For multi-process, use shared memory or external store (Redis).
**Severity:** Low — by design for v1.

### L-2: CSRF Double-Submit Cookie Requires Session

**Description:** CSRF token generation uses `session_id + timestamp` as HMAC input. If no session exists, CSRF protection is weaker (falls back to timestamp-only).
**Workaround:** Ensure session middleware runs before CSRF middleware. Session creation is outside this feature's scope.
**Severity:** Medium — auth-dependent features need session infrastructure.

### L-3: AOP Weaving Requires Compiled Mode

**Description:** The main security-AOP path is still compile-time MIR weaving. The interpreter now has a narrow verified runtime interception slice for `init(...)` join points, but general security advice execution should still be treated as compiled-mode behavior unless explicitly covered by interpreter tests.
**Workaround:** Use compiled mode (`bin/simple build`) for production security weaving. Treat interpreter-mode interception as feature-specific and test-backed, not as a blanket replacement for compiled weaving.
**Severity:** Medium — the interpreter supports a limited runtime slice, but compiled weaving remains the primary execution model.

### L-4: Capability Policy Not Hot-Reloadable

**Description:** `CapabilityPolicy` is set at session creation time. Changing policies requires creating a new session.
**Workaround:** Use `set_capability_policy()` method on UISession to update at runtime.
**Severity:** Low — policy changes are rare.

### L-5: Security Headers Applied to Response Context, Not Body

**Description:** `SecurityHeadersConfig` builds header key-value pairs, but the async HTTP server's `PhaseResult` pipeline doesn't have a direct response-header injection mechanism. Headers must be applied by a response wrapper at the Content or Log phase.
**Workaround:** The `collect_security_headers()` function returns a list of (name, value) pairs that the server's response builder must apply.
**Severity:** Medium — requires integration with specific server response pipeline.

### L-6: Sanitize HTML Does Not Handle All Unicode Edge Cases

**Description:** `sanitize_html()` escapes the standard 6 characters (`< > & " ' /`) but does not handle exotic Unicode normalization attacks (e.g., fullwidth less-than sign U+FF1C).
**Workaround:** For high-security contexts, combine with a Content-Security-Policy header that blocks inline scripts.
**Severity:** Low — CSP headers provide defense-in-depth.

### L-7: Capsule SDN Parsing Is Line-Based

**Description:** The capsule.sdn parser uses a line-based custom parser (not the full SDN parser) due to runtime bootstrapping constraints. This limits SDN features available in capsule configs.
**Workaround:** Keep capsule.sdn configs simple — one key-value per line, list items with `- ` prefix.
**Severity:** Low — consistent with existing MDSOC config parsing.

## Not Implemented (Intentionally Out of Scope)

| Feature | Reason |
|---------|--------|
| Formal verification of parser | Research phase — not v1 |
| Signed binary verification | Supply chain security — future milestone |
| Certificate pinning | TLS-level feature — existing TLS module sufficient |
| Full WAF rules engine | Middleware stack covers OWASP top 10 basics |
| OAuth2/OIDC provider | Existing OAuth client is sufficient for v1 |
