# Security Library Guide

The security library provides cross-cutting security for Simple applications via MDSOC/AOP. Security concerns are woven at compile time — business modules contain zero security code.

## Quick Start

```simple
use std.security.sanitize.{sanitize_html, sanitize_url, sanitize_path}
use std.security.types.{SecurityEvent, AuditEntry, SecurityContext}
use std.security.audit_log.{log_security_event, format_audit_entry}
```

## Module Layout

```
std.security
├── types           # SecurityEvent, AuditEntry, SecurityContext, AuditConfig
├── audit_log       # Structured JSON audit logging
├── sanitize        # HTML, URL, path, identifier sanitization
└── aspects/        # AOP advice (woven automatically)
    ├── audit_advice      # Around/After: request + auth logging
    ├── auth_advice       # Before: authentication checks
    └── validation_advice # Around: output sanitization
```

## Input Sanitization

### HTML (XSS Prevention)

```simple
use std.security.sanitize.{sanitize_html, sanitize_attribute, strip_html_tags}

val safe = sanitize_html("<script>alert('xss')</script>")
# → "&lt;script&gt;alert(&#x27;xss&#x27;)&lt;&#x2F;script&gt;"

val attr_safe = sanitize_attribute("value\" onclick=\"hack()")
# → "value&quot; onclick=&quot;hack()"

val plain = strip_html_tags("<p>Hello <b>world</b></p>")
# → "Hello world"
```

### URL Validation

```simple
use std.security.sanitize.{sanitize_url}

val ok = sanitize_url("https://example.com")     # Ok("https://example.com")
val bad = sanitize_url("javascript:alert(1)")     # Err("dangerous URL scheme: javascript")
val rel = sanitize_url("/page/about")             # Ok("/page/about")
```

Rejected schemes: `javascript:`, `data:`, `vbscript:`, `blob:`.

### Path Traversal Prevention

```simple
use std.security.sanitize.{sanitize_path, is_path_traversal}

val safe = sanitize_path("/home/user/docs/file.txt")  # Ok(...)
val bad = sanitize_path("../../etc/passwd")            # Err("path traversal detected")

# Direct check
is_path_traversal("../secret")     # true
is_path_traversal("%2e%2e/secret") # true (URL-encoded)
is_path_traversal("/normal/path")  # false
```

### Identifier Sanitization

```simple
use std.security.sanitize.{sanitize_identifier}

val ok = sanitize_identifier("user_name")   # Ok("user_name")
val bad = sanitize_identifier("table; DROP") # Err("invalid character...")
val num = sanitize_identifier("1bad")        # Err("must not start with a digit")
```

Whitelist: `[a-zA-Z0-9_]`, max 128 chars, must not start with digit.

## Audit Logging

The audit system logs structured JSON entries for security events. In production, AOP aspects handle this automatically — you rarely call it directly.

### Security Events

```simple
use std.security.types.{SecurityEvent, SecuritySeverity, AuditEntry, AuditConfig}

# Event types and their severity:
# Info:     AuthSuccess, SessionCreated, InputSanitized, RequestProcessed, SessionExpired
# Warning:  AuthFailure, AccessDenied, CapabilityDenied
# Critical: CsrfViolation
```

### Manual Logging (when needed)

```simple
use std.security.types.{SecurityEvent, AuditEntry, AuditConfig}
use std.security.audit_log.{log_security_event}

val event = SecurityEvent.AuthFailure(
    user: "alice",
    peer: "10.0.0.5",
    reason: "invalid password"
)
val entry = AuditEntry.new(
    event: event,
    correlation_id: "req-abc-123",
    module_path: "auth.login"
)
log_security_event(entry, AuditConfig.default())
```

### JSON Output Format

```json
{"timestamp_ms":1711590000,"severity":"warning","event":"auth_failure","correlation_id":"req-abc-123","module":"auth.login","data":{"user":"alic****","peer":"10.0.0.5","reason":"invalid password"}}
```

Secrets are masked automatically when `mask_secrets: true` (default).

### Audit Config

```simple
val config = AuditConfig(
    enabled: true,
    log_file: "security_audit.log",  # File path (append mode)
    log_to_stdout: false,
    min_severity: SecuritySeverity.Warning,  # Skip Info events
    mask_secrets: true
)
```

## UI Capability Enforcement

### Capability Enum

20 capabilities grouped by category:

| Category | Capabilities |
|----------|-------------|
| Input | Mouse, Touch |
| Display | Color, Images, FullScreen |
| UI Chrome | NativeDialogs, Notification, SystemTray |
| Security | FileSystemRead, FileSystemWrite, NetworkAccess, ClipboardRead, ClipboardWrite, Camera, Microphone, Geolocation |
| Developer | DevTools |
| External | ExternalUrls, ShellAccess, ProcessSpawn |

### Default-Deny Policy

```simple
use common.ui.capability.{Capability}
use common.ui.capability_policy.{CapabilityPolicy, check_capability, grant, deny}

# Default-deny: nothing allowed
var policy = CapabilityPolicy.new("main_window")

# Grant specific capabilities
policy = grant(policy, Capability.Notification)
policy = grant(policy, Capability.FileSystemRead)
policy = grant(policy, Capability.ClipboardRead)

# Explicitly deny dangerous ones
policy = deny(policy, Capability.ShellAccess)

# Check
val result = check_capability(policy, Capability.FileSystemRead)
# → Ok(true)

val blocked = check_capability(policy, Capability.ProcessSpawn)
# → Err("Capability ProcessSpawn not granted for window main_window")
```

### SDN Config File

```
# window_main.capability.sdn
window:
    id: main
    default: deny
    granted:
        - Notification
        - FileSystemRead
        - ClipboardRead
        - Mouse
        - Color
        - Images
    denied:
        - ShellAccess
        - ProcessSpawn
        - DevTools
```

```simple
use common.ui.capability_config.{load_capability_config}

val policy = load_capability_config("window_main.capability.sdn", "main")
```

### Session Integration

```simple
use common.ui.session.{UISession}
use common.ui.capability_policy.{CapabilityPolicy, grant}

# Create session with policy
var policy = CapabilityPolicy.new("main")
policy = grant(policy, Capability.Mouse)
policy = grant(policy, Capability.Color)

val session = UISession.new_with_policy(tree, policy)

# Check capability from session
session.check_cap(Capability.Mouse)           # Ok(true)
session.check_cap(Capability.ShellAccess)     # Err(...)

# Gated surface open
session.open_surface_gated("popup", tree, Capability.FullScreen)  # Err if FullScreen not granted
```

## HTTP Security Middleware

All middleware plug into the async HTTP server's phase pipeline.

### Enable All Security Middleware

```simple
use std.http_server.rate_limit.{RateLimitConfig, RateLimitStore, rate_limit_handler}
use std.http_server.request_validation.{RequestValidationConfig, request_validation_handler}
use std.http_server.csrf.{CsrfConfig, csrf_handler}
use std.http_server.cors.{CorsConfig, cors_handler}
use std.http_server.security_headers.{SecurityHeadersConfig, security_headers_handler}
```

### Rate Limiting

```simple
val config = RateLimitConfig(
    requests_per_window: 100,  # Max requests per window
    window_ms: 60000,          # 1 minute window
    burst_size: 20,            # Allow bursts
    exempt_paths: ["/health", "/metrics"]
)
# Returns 429 "Rate limit exceeded" when limit hit
```

### CSRF Protection

```simple
val config = CsrfConfig(
    secret_key: "your-server-secret",
    token_header: "X-CSRF-Token",
    cookie_name: "csrf_token",
    exempt_paths: ["/api/webhook"],
    exempt_methods: ["GET", "HEAD", "OPTIONS"]
)
# Uses HMAC-SHA256 double-submit cookie pattern
# Returns 403 "CSRF validation failed" on mismatch
```

### CORS

```simple
val config = CorsConfig(
    allowed_origins: ["https://app.example.com"],
    allowed_methods: ["GET", "POST", "PUT", "DELETE"],
    allowed_headers: ["Content-Type", "Authorization"],
    expose_headers: [],
    allow_credentials: true,
    max_age_seconds: 3600
)
# Returns 403 "Origin not allowed" for blocked origins
```

### Security Headers

```simple
val config = SecurityHeadersConfig.default()
# Adds to every response:
# Content-Security-Policy: default-src 'self'; script-src 'self'; style-src 'self' 'unsafe-inline'
# X-Content-Type-Options: nosniff
# X-Frame-Options: DENY
# Strict-Transport-Security: max-age=31536000; includeSubDomains
# Referrer-Policy: strict-origin-when-cross-origin
```

### Pipeline Order

```
Request → [Rate Limit] → [Request Validation] → [CSRF] → [CORS] → [Security Headers] → Handler
           PreRead:100     Read:90               Access:150 Access:180 Access:200
```

## MDSOC Security Dimension

Security is a first-class MDSOC dimension with 5 layers:

```
┌─────────────────────────┐
│ audit    (highest)      │  Observes all via AOP weaving
├─────────────────────────┤
│ auth                    │  Session, CSRF, identity
├─────────────────────────┤
│ validation              │  Input sanitization, request checks
├─────────────────────────┤
│ enforcement             │  Capability gates, permissions
├─────────────────────────┤
│ crypto   (lowest)       │  Pure primitives (HMAC, SHA, random)
└─────────────────────────┘
```

Layer rules: lower layers cannot depend on upper layers. The audit layer observes through AOP weaving, not direct imports.

### AOP Aspects (Automatic)

These are woven at compile time — you don't call them manually:

| Aspect | Form | What It Does | Predicate |
|--------|------|-------------|-----------|
| audit_advice | Around | Logs HTTP request duration + result | `execution(*.handle_request) & within(http_server.**)` |
| audit_advice | AfterSuccess | Logs auth successes | `execution(*.authenticate*)` |
| audit_advice | AfterError | Logs auth failures | `execution(*.authenticate*)` |
| auth_advice | Before | Checks `@requires_auth` | `attr(requires_auth) & within(http_server.**)` |
| validation_advice | Around | Sanitizes HTML render output | `execution(*.render_html*) & within(ui.**)` |
| validation_advice | Before | Validates `@validates_input` | `attr(validates_input) & within(http_server.**)` |

### Using @requires_auth

```simple
@requires_auth
fn get_user_profile(request: HttpRequestData) -> PhaseResult:
    # Auth check is woven automatically before this runs
    # If SecurityContext is not authenticated, returns 401
    pass_todo("implement profile handler")
```

## Security Context

```simple
use std.security.types.{SecurityContext}

# Anonymous context (no auth)
val ctx = SecurityContext.anonymous("10.0.0.1")
ctx.is_authenticated()    # false
ctx.has_capability("fs")  # false

# Authenticated context
val auth_ctx = SecurityContext(
    peer_addr: "10.0.0.1",
    session_id: "sess-abc",
    user_id: "alice",
    correlation_id: "req-123",
    capabilities: ["fs_read", "notification"]
)
auth_ctx.is_authenticated()         # true
auth_ctx.has_capability("fs_read")  # true
```

## Related Documents

- [Design](../../design/security_aop.md) — Architecture diagrams and type definitions
- [Requirements](../../plan/requirement/security_aop.md) — Acceptance criteria
- [NFR](../../plan/nfr/security_baseline.md) — Performance and quality targets
- [Research](../../research/security_aop_architecture_2026-03-28.md) — Gap analysis and decisions
- [Limitations](../../tracking/bug/security_aop_limitations.md) — Known limitations
