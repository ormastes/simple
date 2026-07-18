# Fail-Closed Security Model

Developer guide for writing security components in Simple. These invariants are
enforced by existing runtime code; violating them introduces security holes that
bypass the entire AOP and capability layer.

---

## 1. Security Advice Must Return `Result` and Fail Closed

Every before-advice registered with the MDSOC weaving engine **must** return
`Result<(), text>`. The weaver's `is_err()` gate aborts the gated call
immediately on `Err`. A function that returns `()` (void) or that swallows an
error silently grants access.

**Correct pattern:**

```simple
fn check_auth_before(ctx: JoinPointContext) -> Result<(), text>:
    val sec_ctx = resolve_security_context(ctx)
    if not sec_ctx.is_authenticated():
        # log, then ...
        return Err("authentication required for {ctx.function_name}")
    Ok(())
```

**Wrong — void return means the weaver can never abort:**

```simple
fn check_auth_before(ctx: JoinPointContext):   # BAD: no Result
    ...
```

The three built-in before-advices (`check_auth_before`, `check_capability_before`,
`deny_all_before`) all return `Result<(), text>` and are the canonical reference:

- `src/lib/nogc_sync_mut/security/aspects/auth_advice.spl`
- `src/lib/nogc_sync_mut/security/aspects/deny_advice.spl`

`deny_all_before` is wired into `weaving_config` as a before-advice and
unconditionally returns `Err("endpoint is in maintenance mode")`.

---

## 2. Capability Parsing Is Fail-Closed — `Err` Means Deny

`parse_capability` in `src/lib/nogc_sync_mut/security/enforcement/capability.spl`
returns `Result<Capability, text>`. On any malformed or unrecognised input it
returns `Err`. **Callers must treat `Err` as deny** — never fall back to a
wildcard or permissive default.

```simple
val cap = parse_capability(raw_string)
if cap.is_err():
    return Err("unknown capability — access denied")
```

Before this fix, unknown kind strings silently produced
`Custom(scope:"*")` — a wildcard grant. That path is gone; `Err` is now the
only outcome for unknown kinds.

---

## 3. Default-Deny Capability Policy

The `CapabilityStore` grants no permissions at construction. A principal holds
a capability only when a non-expired, explicitly-issued grant exists. There is
no ambient capability. All grant methods validate that `expiry_ms` is in the
future before accepting the grant.

---

## 4. Capability Path Boundaries Use Separator Checks

`_capability_path_allowed(scope, path)` requires either an exact match or that
`path` starts with `scope + "/"`. A `/data` scope does **not** authorise a
request to `/data-evil` — the separator makes the boundary unambiguous.

```simple
fn _capability_path_allowed(scope: text, path: text) -> bool:
    scope == "*" or path == scope or path.starts_with(scope + "/")
```

---

## 5. Web / HTTP Middleware Invariants

### CORS

- `"null"` origin is always rejected regardless of the allowlist (prevents
  sandboxed-iframe CSRF attacks).
- `allow_credentials: true` combined with a wildcard `"*"` origin is blocked —
  the handler returns `403` before headers are emitted.
- When the allowlist contains only `"*"`, the literal string `"*"` is written
  into `Access-Control-Allow-Origin`; the request `Origin` is **never**
  reflected. This prevents credentialed-reflection attacks.

### CSRF

- Token comparison uses HMAC-SHA256. The comparison is constant-time (HMAC
  equality is timing-safe by construction). Do not replace with a plain string
  equality on CSRF tokens.

### Header Injection

- Response headers must not include literal `\r` or `\n` characters. The header
  builder layer must reject or strip CRLF from any value derived from user input
  before writing it into an HTTP response line.

### HSTS

- `max-age` is clamped; values exceeding the policy maximum are silently reduced.
- Setting `max-age=0` to revoke HSTS is permitted.

### Content Security Policy

- The default CSP does not include `unsafe-inline` or `unsafe-eval`. If you need
  either for a specific endpoint, set it explicitly in a per-handler override and
  note the security trade-off in a comment.

Source: `src/lib/nogc_async_mut/http_server/cors.spl`,
`src/lib/nogc_async_mut/http_server/csrf.spl`,
`src/lib/nogc_async_mut/http_server/headers.spl`.

---

## 6. Sanitizers Are Allowlist-Based

`sanitize_url` in `src/lib/nogc_sync_mut/security/sanitize.spl` accepts only
`http://`, `https://`, `/`-relative, and `#`-anchor forms. Everything else —
including `javascript:`, `data:`, `ftp:`, `gopher:`, `vbscript:`, `blob:`,
`file:` — returns `Err`.

`UrlValidator` in `src/lib/nogc_sync_mut/security/validation/url_validator.spl`:

- Scheme allowlist: only `http` and `https` by default.
- SSRF: strips `user@` userinfo and rejects `%`-encoded hostnames.
- Private IP ranges (`10.0.0.0/8`, `172.16.0.0/12`, `192.168.0.0/16`,
  `127.0.0.0/8`, `169.254.0.0/16`, `::1`, `fd00::/8`, `fe80::/10`) are blocked
  by default.
- When `allowed_hosts` is non-empty, only listed hosts are permitted.

`_sanitize_log_field` in `src/lib/common/security/audit_log.spl` strips `\r`,
`\n`, and `\t` from every user-controlled value before it is written into an
audit-log line. All fields in every `SecurityEvent` variant pass through this
sanitizer.

---

## See Also

- `doc/04_architecture/infra/security/security_convention_first_architecture.md` —
  layer model, capability handles, sandbox lowering.
- `doc/09_report/security_hardening_audit_2026-06-11.md` — audit report with
  full finding details.
- `test/01_unit/lib/security/security_hardening_regression_spec.spl` —
  regression specs locking in these invariants.
