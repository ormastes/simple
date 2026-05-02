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
