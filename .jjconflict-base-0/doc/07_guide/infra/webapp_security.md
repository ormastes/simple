# Web Application Security Guide

Security architecture for SimpleWeb applications. The framework is designed so that **forgetting security = safe** (fail-closed, default-deny).

---

## Security Model: Default-Deny with AOP

The SimpleWeb framework uses compile-time AOP weaving to enforce security. The MDSOC security dimension has 5 layers:

```
crypto (SHA, bcrypt, AES, HMAC, Ed25519)
    |
enforcement (capabilities, permissions, rate limiting)
    |
validation (input sanitization, URL validation, prompt sanitization)
    |
auth (authentication, sessions, CSRF tokens)
    |
audit (structured logging, secret masking)
```

### Key Principle: Unannotated Handlers Require Auth

If you write a handler function without any security annotation, the AOP weaving engine treats it as `@requires_auth`. This means:

- Forgetting to add `@public` to a route = route requires authentication (safe)
- Forgetting to add `@requires_capability` = route still requires basic auth (safe)
- You must **explicitly opt in** to public access with `@public`

### Security Annotations

| Annotation | Effect | Use When |
|-----------|--------|----------|
| `@public` | No auth required | Landing pages, login forms, public API |
| `@requires_auth` | Must be authenticated | User-specific pages (default for unannotated) |
| `@requires_capability("X")` | Must hold capability X | Admin pages, privileged operations |
| `@deny_all` | Unconditional reject | Maintenance mode |

---

## Capability-Based Access Control

Capabilities are grant-based (not role-based). Each grant has:
- **Principal**: who holds the capability
- **Capability**: what they can do (Read, Write, Execute, Admin, Network, FileSystem, Database, Custom)
- **Expiry**: mandatory expiry time (no perpetual grants)
- **Delegatable**: whether the principal can sub-grant

```simple
use std.security.enforcement.capability.{CapabilityStore, Capability}

var store = CapabilityStore.new()
store.grant("user123", Capability.Read("packages"), "admin", expiry_ms: 86400000)?
store.grant("user123", Capability.Write("packages"), "admin", expiry_ms: 86400000)?

# Check
val can_read = store.check("user123", Capability.Read("packages"))  # true
val can_admin = store.check("user123", Capability.Admin("system"))  # false (denied)
```

### Grant Delegation Rules
- Non-delegatable (default): use but cannot grant to others
- Delegatable: can create non-delegatable sub-grants (max depth 2)
- Admin: can create delegatable grants
- All grants expire — no perpetual access

---

## CSRF Protection

All state-changing requests (POST, PUT, DELETE) should include a CSRF token:

```simple
# Controller: generate token
val token = csrf_token_for_session(session_id, app_secret)

# Template: include in form
<form method="POST" action="/todos">
    {{{csrf_field}}}
    <input name="title" type="text">
    <button type="submit">Create</button>
</form>
```

The framework verifies CSRF tokens automatically via the existing `csrf.spl` middleware.

**Fail-closed on misconfiguration (2026-06-11):** an empty `secret_key` makes
HMAC tokens forgeable, so `csrf_handler` now **denies** state-changing requests
when `secret_key == ""`, and `generate_csrf_token*` refuse to mint a token under
an empty key. Always set a real `secret_key` from a secret store — a missing key
is a deny, not a silent pass. Token comparison uses the canonical
`std.common.crypto.constant_time_compare` (no per-module timing-unsafe copies).

---

## CORS & Cache Safety

When a CORS response reflects a **specific** request Origin (not the literal
`*`), it must also send `Vary: Origin`. Without it a shared/CDN cache can serve
one origin's allowed response to a different origin. The middleware
(`add_cors_headers`) and the access-phase `cors_handler` add `Vary: Origin`
automatically for reflected origins and skip it for the origin-independent `*`.

```simple
# Wildcard + credentials is rejected (credentialed reflection bypass);
# a reflected concrete origin always carries Vary: Origin.
val cors = CorsConfig.default()   # allowed_origins must be an explicit allowlist
```

Rules enforced: wildcard `*` + `Allow-Credentials: true` is refused, a literal
`null` Origin is refused, and CRLF in any header value is rejected.

---

## Rate Limiting & Trusted Proxies

Rate limiting keys on the **direct socket peer** (`peer_addr`) by default.
`X-Forwarded-For` is only consulted when the direct peer is a configured trusted
proxy — otherwise a client could spoof XFF to evade limits or frame another
address.

```simple
val config = RateLimitConfig(
    requests_per_window: 100, window_ms: 60000, burst_size: 20,
    exempt_paths: ["/health"],
    trusted_proxies: ["10.0.0.1"]   # only this peer's XFF is believed; [] = ignore XFF
)
```

With the default empty `trusted_proxies`, behavior is unchanged and spoof-safe:
the limiter always keys on `peer_addr`. When the peer is trusted, the XFF chain
is walked right-to-left and the first non-proxy hop is taken as the client.
`trusted_proxies` entries must match the `peer_addr` string format exactly.

---

## Simple Web Browser Production Boundary

`src/app/ui.web` is the served Simple Web/browser boundary, so production mode
must fail closed before it mints tokens or upgrades WebSockets:

- `SIMPLE_UI_WEB_TOKEN_SECRET` is required for production token signing.
- `SIMPLE_UI_WEB_ALLOW_INSECURE_DEV_SECRET=1` is only for explicit non-TLS local
  development fallback.
- TLS serving must never use the insecure dev secret fallback.
- `/ui/login` requires an allowed `Origin` and is bounded by body-size and
  fixed-window burst gates.
- `/ui/ws`, `/ui/resume`, and sensitive `/api/*` routes require an
  origin-bound bearer token; legacy `/ws` is hidden with `404`.
- Browser clients should carry bearer tokens in `Sec-WebSocket-Protocol`;
  query-string bearer extraction is deprecated and non-authorizing, including
  when `SIMPLE_UI_WEB_ALLOW_QUERY_TOKEN=1` is present.
- The selected production-hardening scope is Feature Option C plus NFR Option C
  in `doc/02_requirements/feature/simple_web_browser_production_hardening.md`
  and `doc/02_requirements/nfr/simple_web_browser_production_hardening.md`.

Focused evidence:

```bash
bin/simple test test/03_system/gui/simple_web_browser_production_hardening_spec.spl --mode=interpreter --clean --timeout 360
```

The implementation report is
`doc/09_report/simple_web_browser_production_hardening.md`.

---

## IDOR Prevention

Always verify resource ownership before allowing access:

```simple
fn action_edit(ctx: ControllerContext) -> HttpResponseData:
    val todo = find_todo(ctx.params.get("id"))?
    # CRITICAL: verify ownership
    if todo.user_id != ctx.current_user_id:
        return render_error(403, "Forbidden")
    render_page(ctx, "todos/edit", ...)
```

The `SEC-AUTH001` lint rule warns when handlers lack security annotations, but IDOR checks require manual implementation per resource.

---

## SQL Injection Prevention

The framework enforces parameterized queries. The `SEC-SQL001` lint rule (deny level) catches string interpolation with SQL keywords:

```simple
# BAD — lint error SEC-SQL001
val sql = "SELECT * FROM users WHERE id = {id}"

# GOOD — parameterized query
val rows = db.query("SELECT * FROM users WHERE id = ?", [DbValue.Integer(id)])?
```

Use `QueryBuilder` or `Repository<T>` for all database operations.

---

## XSS Prevention

Templates auto-escape all `{{var}}` output. Raw output `{{{var}}}` triggers lint warning `SEC-XSS001`.

```html
<!-- Safe (auto-escaped) -->
<p>{{user_input}}</p>

<!-- Dangerous (raw) — requires @allow(raw_html) -->
<div>{{{raw_html}}}</div>
```

---

## Secret Management

See `doc/07_guide/security/secret_prevention.md` for complete guide.

Key rules:
1. **Never hardcode secrets** — use environment variables
2. **Use `.env.example`** as schema (no values), `.env` for actual values (gitignored)
3. **Pre-commit hook** blocks commits containing secret patterns
4. **CredentialHandle** type prevents accidental logging of credentials
5. **Audit log masking** automatically masks sensitive values
6. **Cryptographic randomness** — tokens, session IDs, salts and keys use
   `random_hex`/`random_bytes` → `rt_random_hex`, backed by the OS CSPRNG
   (`OsRng` in interpreter mode, `/dev/urandom` in the compiled runtime). The
   LCG generator (`std.random` / `random_pure`) is **non-cryptographic** — never
   use it for secrets, tokens, or nonces.

---

## URL Validation (SSRF Prevention)

Validate all URLs from user input before fetching:

```simple
use std.security.validation.url_validator.{validate_url}

fn action_fetch(ctx: ControllerContext) -> HttpResponseData:
    val url = ctx.params.get("url") ?? ""
    validate_url(url)?  # rejects private IPs, localhost, non-HTTP(S)
    val response = http_get(url)?
    render_json(response.body)
```

Blocked destinations: `10.0.0.0/8`, `172.16.0.0/12`, `192.168.0.0/16`, `127.0.0.0/8`, `169.254.0.0/16`, `::1`, `fd00::/8`

---

## Prompt Injection Prevention

If your webapp uses LLM features:

```simple
use std.security.validation.prompt_sanitizer.{PromptSanitizer}

var sanitizer = PromptSanitizer(
    delimiter: "---USER INPUT---",
    max_input_length: 10000,
    blocked_patterns: ["ignore previous", "system prompt"]
)

val safe_input = sanitizer.sanitize_input(user_input)
val wrapped = sanitizer.wrap_user_input(safe_input)
```

---

## Password Hashing

Always use bcrypt (available via `std.bcrypt`):

```simple
use std.bcrypt.{bcrypt_hash, bcrypt_verify}

val hash = bcrypt_hash(password, cost: 12)
val valid = bcrypt_verify(password, hash)
```

The `SEC-CMP001` lint rule warns when `==` is used on variables named `password`, `token`, `secret`, etc.

---

## Compiler Security Lint Rules

Run `bin/simple build lint` to check for security issues:

| Code | Level | What It Catches |
|------|-------|-----------------|
| SEC-SQL001 | deny | SQL injection via string interpolation |
| SEC-SEC001-008 | deny | Hardcoded API keys, tokens, private keys |
| SEC-CMP001 | warn | Timing-vulnerable password comparison |
| SEC-XSS001-003 | warn | Raw HTML output without annotation |
| SEC-AUTH001 | warn | HTTP handler without security annotation |
| SEC-SSRF001-002 | warn | User-controlled URLs in fetch calls |

---

## Package Signing

Published packages are signed with Ed25519:

```bash
# Generate signing key
simple keygen                    # creates ~/.simple/signing_key.pem + .pub

# Publish (auto-signs)
simple publish                   # signs .spk with private key

# Install (auto-verifies)
simple install my-package        # verifies signature + checksum
```

Trust levels: Registry-trusted, User-trusted, Untrusted. Use `simple trust add <fingerprint>` to trust a signer.

---

## Security Checklist

- [ ] All public routes explicitly annotated `@public`
- [ ] All forms include CSRF token
- [ ] Resource access checks ownership (IDOR prevention)
- [ ] Database queries use parameterized SQL
- [ ] Passwords hashed with bcrypt
- [ ] Secrets in environment variables, not source code
- [ ] Pre-commit hook installed (`scripts/secret-scan.shs`)
- [ ] User input validated before URL fetching
- [ ] Template output auto-escaped (no raw unless annotated)
- [ ] API tokens use JWT with expiry
- [ ] Session cookies are HttpOnly + Secure + SameSite
- [ ] CSRF `secret_key` is set from a secret store (empty key = deny, not pass)
- [ ] CORS reflects only allowlisted origins; reflected origins send `Vary: Origin`
- [ ] Rate-limit `trusted_proxies` set only for real proxies (default keys on peer)
- [ ] Tokens/session IDs/salts use `random_hex` (CSPRNG), never `std.random` (LCG)
