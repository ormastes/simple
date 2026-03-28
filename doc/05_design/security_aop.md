# Security AOP Architecture -- Design

**Date:** 2026-03-28
**Status:** Implemented
**Requirement:** [doc/02_requirements/feature/security_aop.md](../plan/requirement/security_aop.md)
**Research:** [doc/01_research/security_aop_architecture_2026-03-28.md](../research/security_aop_architecture_2026-03-28.md)

## 1. Module Structure

```
src/lib/common/security/
    types.spl                     # SecurityEvent, AuditEntry, SecurityContext, AuditConfig
    audit_log.spl                 # Structured JSON audit logging
    sanitize.spl                  # Input sanitization (HTML, URL, path, identifier)
    capsule.sdn                   # MDSOC 5-layer dimension definition + weaving rules
    aspects/
        audit_advice.spl          # Around/AfterSuccess/AfterError audit AOP advice
        auth_advice.spl           # Before auth/capability AOP advice
        validation_advice.spl     # Around/Before validation AOP advice

src/lib/common/ui/
    capability.spl                # Capability enum (20 variants) + NotSupported
    capability_policy.spl         # Default-deny policy engine
    capability_config.spl         # SDN config parser for per-window policies
    session.spl                   # UISession (modified: capability_policy field)

src/lib/nogc_async_mut/http_server/
    rate_limit.spl                # Token bucket rate limiting (PreRead phase)
    request_validation.spl        # Path/header/URI validation (Read phase)
    csrf.spl                      # HMAC-SHA256 CSRF double-submit (Access phase)
    cors.spl                      # CORS origin enforcement (Access phase)
    security_headers.spl          # CSP/HSTS/X-Frame-Options injection (Access phase)

src/app/
    ui.tauri/backend.spl          # Modified: capability enforcement before IPC ops
    ui.ipc/protocol.spl           # Modified: IPC message size/structure validation

src/compiler/85.mdsoc/weaving/
    weaving_config.spl            # Modified: weavingconfig_with_security_aspects()
    join_point_kind.spl           # Modified: SecurityGate variant added
```

## 2. Type Definitions

### Security Core (`src/lib/common/security/types.spl`)

```simple
enum SecurityEvent:
    AuthSuccess(user: text, peer: text)
    AuthFailure(user: text, peer: text, reason: text)
    AccessDenied(resource: text, capability: text, peer: text)
    CsrfViolation(peer: text, path: text)
    RateLimitHit(peer: text, path: text)
    InputSanitized(field: text, original_len: i64)
    SessionCreated(session_id: text, peer: text)
    SessionExpired(session_id: text)
    CapabilityDenied(capability: text, window_id: text)
    RequestProcessed(path: text, duration_ms: i64, status: i64)

enum SecuritySeverity:
    Info
    Warning
    Critical

class AuditEntry:
    timestamp_ms: i64
    event: SecurityEvent
    correlation_id: text
    module_path: text
    severity: SecuritySeverity

class SecurityContext:
    peer_addr: text
    session_id: text
    user_id: text
    correlation_id: text
    capabilities: List<text>

class AuditConfig:
    enabled: bool
    log_file: text
    log_to_stdout: bool
    min_severity: SecuritySeverity
    mask_secrets: bool
```

### UI Capabilities (`src/lib/common/ui/capability.spl`)

```simple
enum Capability:
    # Input (2)
    Mouse, Touch
    # Display (3)
    Color, Images, FullScreen
    # UI Chrome (3)
    NativeDialogs, Notification, SystemTray
    # Security-gated resources (7)
    FileSystemRead, FileSystemWrite, NetworkAccess,
    ClipboardRead, ClipboardWrite, Camera, Microphone, Geolocation
    # Developer (1)
    DevTools
    # External access (3)
    ExternalUrls, ShellAccess, ProcessSpawn

class NotSupported:
    operation: text
```

### Capability Policy (`src/lib/common/ui/capability_policy.spl`)

```simple
class CapabilityPolicy:
    window_id: text
    granted: List<Capability>
    denied: List<Capability>
    default_deny: bool
    audit_config: AuditConfig
```

### HTTP Security Middleware Configs

```simple
# rate_limit.spl
class RateLimitConfig:
    requests_per_window: i64
    window_ms: i64
    burst_size: i64
    exempt_paths: [text]

class RateLimitStore:
    peers: [text]
    tokens: [i64]
    last_refill_ms: [i64]

# csrf.spl
class CsrfConfig:
    secret_key: text
    token_header: text
    cookie_name: text
    exempt_paths: [text]
    exempt_methods: [text]

# cors.spl
class CorsConfig:
    allowed_origins: [text]
    allowed_methods: [text]
    allowed_headers: [text]
    expose_headers: [text]
    allow_credentials: bool
    max_age_seconds: i64

# security_headers.spl
class SecurityHeadersConfig:
    enable_csp: bool
    csp_value: text
    enable_content_type_options: bool
    enable_frame_options: bool
    frame_options_value: text
    enable_hsts: bool
    hsts_max_age: i64
    hsts_include_subdomains: bool
    enable_referrer_policy: bool
    referrer_policy_value: text
```

### MDSOC Weaving Extension (`src/compiler/85.mdsoc/weaving/join_point_kind.spl`)

```simple
enum JoinPointKind:
    Execution(function_name: text, signature: text)
    Decision(location: text)
    Condition(location: text)
    Error(location: text, error_type: text)
    SecurityGate(capability: text, resource: text)   # NEW
```

## 3. API Surface

### Audit Logging (`audit_log.spl`)

| Function | Signature | Description |
|----------|-----------|-------------|
| `log_security_event` | `(entry: AuditEntry, config: AuditConfig)` | Log entry to file/stdout per config |
| `format_audit_entry` | `(entry: AuditEntry, mask_secrets: bool) -> text` | Serialize entry as structured JSON |
| `mask_value` | `(value: text) -> text` | Show first 4 chars, mask rest with `****` |
| `severity_for_event` | `(event: SecurityEvent) -> SecuritySeverity` | Map event to severity level |

### Input Sanitization (`sanitize.spl`)

| Function | Signature | Description |
|----------|-----------|-------------|
| `sanitize_html` | `(input: text) -> text` | Escape `< > & " ' /` for XSS prevention |
| `sanitize_attribute` | `(input: text) -> text` | Escape for HTML attribute context |
| `sanitize_url` | `(input: text) -> Result<text, text>` | Reject `javascript:`, `data:`, `blob:` schemes |
| `sanitize_identifier` | `(input: text) -> Result<text, text>` | Whitelist `[a-zA-Z_][a-zA-Z0-9_]*`, max 128 |
| `sanitize_path` | `(input: text) -> Result<text, text>` | Reject traversal, null bytes, >4096 len |
| `is_path_traversal` | `(path: text) -> bool` | Detect `..`, `%2e%2e`, null byte patterns |
| `validate_content_type` | `(header: text, expected: text) -> bool` | Media type match ignoring params |
| `strip_html_tags` | `(input: text) -> text` | Remove all HTML tags from text |
| `truncate` | `(input: text, max_len: i64) -> text` | Truncate with `...` ellipsis |

### AOP Advice -- Audit (`aspects/audit_advice.spl`)

| Function | Form | Woven At |
|----------|------|----------|
| `log_request_advice` | Around | `execution(*.handle_request) & within(std.http.**)` |
| `log_auth_success_advice` | AfterSuccess | `execution(*.authenticate) & within(std.security.auth.**)` |
| `log_auth_failure_advice` | AfterError | `execution(*.authenticate) & within(std.security.auth.**)` |

### AOP Advice -- Auth (`aspects/auth_advice.spl`)

| Function | Form | Woven At |
|----------|------|----------|
| `check_auth_before` | Before | `execution(*.handle_request) & annotation(@requires_auth)` |
| `check_capability_before` | Before | `execution(*.handle_request) & annotation(@requires_capability)` |

### AOP Advice -- Validation (`aspects/validation_advice.spl`)

| Function | Form | Woven At |
|----------|------|----------|
| `sanitize_html_output` | Around | `execution(*.render) & within(std.ui.**)` |
| `validate_request_input` | Before | `execution(*.handle_request) & within(std.http.**)` |

### Capability Policy (`capability_policy.spl`)

| Function | Signature | Description |
|----------|-----------|-------------|
| `check_capability` | `(policy: CapabilityPolicy, cap: Capability) -> Result<bool, text>` | Default-deny check |
| `require_capability` | `(policy: CapabilityPolicy, cap: Capability) -> Result<bool, NotSupported>` | Check returning NotSupported on denial |
| `grant` | `(policy: CapabilityPolicy, cap: Capability) -> CapabilityPolicy` | Add granted capability |
| `deny` | `(policy: CapabilityPolicy, cap: Capability) -> CapabilityPolicy` | Add denied capability |
| `capability_name` | `(cap: Capability) -> text` | Enum to string |
| `parse_capability` | `(name: text) -> Result<Capability, text>` | String to enum |

### Capability Config (`capability_config.spl`)

| Function | Signature | Description |
|----------|-----------|-------------|
| `parse_capability_config` | `(content: text, window_id: text) -> Result<CapabilityPolicy, text>` | Parse SDN text |
| `load_capability_config` | `(path: text, window_id: text) -> Result<CapabilityPolicy, text>` | Load from SDN file |

### HTTP Middleware

| Module | Handler Function | Phase | Priority |
|--------|-----------------|-------|----------|
| `rate_limit` | `rate_limit_handler(request, server_config, config, store) -> PhaseResult` | PreRead | 100 |
| `request_validation` | `request_validation_handler(request, config) -> PhaseResult` | Read | 90 |
| `csrf` | `csrf_handler(request, server_config, config) -> PhaseResult` | Access | 150 |
| `cors` | `cors_handler(request, server_config, config) -> PhaseResult` | Access | 180 |
| `security_headers` | `security_headers_handler(request, server_config, config) -> PhaseResult` | Access | 200 |

Additional HTTP utility functions:

| Module | Function | Signature |
|--------|----------|-----------|
| `csrf` | `generate_csrf_token` | `(config: CsrfConfig, session_id: text) -> text` |
| `cors` | `is_origin_allowed` | `(origin: text, allowed: [text]) -> bool` |
| `security_headers` | `collect_security_headers` | `(config: SecurityHeadersConfig) -> [(text, text)]` |
| `security_headers` | `apply_security_headers` | `(headers: [(text, text)], config: SecurityHeadersConfig) -> [(text, text)]` |

### MDSOC Weaving (`weaving_config.spl`)

| Function | Signature | Description |
|----------|-----------|-------------|
| `weavingconfig_with_security_aspects` | `(base: WeavingConfig) -> WeavingConfig` | Merge 6 security weaving rules into base config |

### IPC Validation (`protocol.spl`)

| Function | Signature | Description |
|----------|-----------|-------------|
| `validate_ipc_message` | `(json_str: text) -> Result<text, text>` | Reject >64KB, empty, non-object |
| `validate_ipc_field` | `(value: text, field_name: text) -> text` | Truncate fields >8KB |

### UISession Extensions (`session.spl`)

| Function | Signature | Description |
|----------|-----------|-------------|
| `UISession.new_with_policy` | `(tree: UITree, policy: CapabilityPolicy) -> UISession` | Session with custom policy |
| `UISession.check_cap` | `(cap: Capability) -> Result<bool, text>` | Delegate to policy engine |
| `UISession.set_capability_policy` | `(policy: CapabilityPolicy)` | Replace policy at runtime |
| `UISession.open_surface_gated` | `(id: text, tree: UITree, required_cap: Capability) -> Result<SurfaceHandle, text>` | Capability-gated surface open |

## 4. Integration Points

### Existing Module Dependencies

```
security/types.spl
    depends on: std.time, std.io.crypto_ffi

security/audit_log.spl
    depends on: security/types, std.json, std.io.file

security/sanitize.spl
    depends on: (pure, no external deps)

security/aspects/*
    depends on: security/types, security/audit_log, security/sanitize,
                compiler.mdsoc.weaving.join_point (JoinPointContext)

ui/capability_policy.spl
    depends on: ui/capability, security/types, security/audit_log

ui/capability_config.spl
    depends on: ui/capability, ui/capability_policy

ui/session.spl
    depends on: ui/capability, ui/capability_policy (NEW)

http_server/{rate_limit,request_validation,csrf}.spl
    depends on: http_server/types, security/types, security/audit_log

http_server/cors.spl, security_headers.spl
    depends on: http_server/types (no security/types dependency)

app/ui.tauri/backend.spl
    depends on: ui/capability_policy (NEW: require_capability calls)

app/ui.ipc/protocol.spl
    depends on: security/sanitize (NEW: sanitize_html, is_path_traversal)

compiler/85.mdsoc/weaving/weaving_config.spl
    depends on: weaving_rule, advice_form (NEW: security rule factory)

compiler/85.mdsoc/weaving/join_point_kind.spl
    (no new dependencies, added SecurityGate variant)
```

### Key Integration Contracts

1. **AOP aspects are never called directly.** The MDSOC weaving engine injects them at MIR level based on join point predicates defined in `capsule.sdn` and `weavingconfig_with_security_aspects()`.

2. **Capability enforcement is opt-in per backend.** `TauriBackend` checks capabilities before `show_notification` and `show_dialog`. `UISession` enforces via `check_cap()` and `open_surface_gated()`.

3. **HTTP middleware plugs into the existing `MiddlewarePipeline` phase system.** Each handler follows the `(HttpRequestData, ServerConfig, ...) -> PhaseResult` contract.

4. **IPC validation is inline.** `parse_ipc_message` calls `validate_ipc_message` before any field extraction. No AOP weaving needed -- validation is structural.

## 5. MDSOC Dimension Architecture

The security dimension is defined in `capsule.sdn` as a horizontal dimension with 5 layers and strict dependency ordering.

```
                    MDSOC Security Dimension
    ============================================================

    Layer 5 (highest)    +----------------------------------+
    AUDIT                | log_security_event               |
                         | format_audit_entry               |
                         | AuditEntry, AuditConfig          |
                         | SecurityEvent, SecuritySeverity  |
                         +----------------------------------+
                                     |  depends on
                                     v
    Layer 4              +----------------------------------+
    AUTH                 | authenticate, create_session     |
                         | verify_csrf_token                |
                         | SecurityContext, SessionToken    |
                         +----------------------------------+
                                     |  depends on
                                     v
    Layer 3              +----------------------------------+
    VALIDATION           | sanitize_html, sanitize_url      |
                         | sanitize_path, sanitize_identifier|
                         | validate_content_type            |
                         | strip_html_tags, truncate        |
                         +----------------------------------+
                                     |  depends on
                                     v
    Layer 2              +----------------------------------+
    ENFORCEMENT          | check_capability                 |
                         | enforce_permission               |
                         | rate_limit_check                 |
                         | csrf_token_validate              |
                         | CapabilityGate, PermissionResult |
                         +----------------------------------+
                                     |  depends on
                                     v
    Layer 1 (lowest)     +----------------------------------+
    CRYPTO               | hash_sha256, hash_sha512         |
                         | hmac_sha256, random_bytes        |
                         | aes_encrypt, aes_decrypt         |
                         | constant_time_compare            |
                         +----------------------------------+
```

**Layer Rules:**
- `direction = "lower_to_upper"` -- lower layers may be imported by higher layers
- `enforce_layering = true` -- compiler rejects upward dependencies (e.g., crypto cannot import audit)
- `reject_cycles = true` -- no circular dependencies between capsules
- `allow_same_layer = true` -- files within the same layer may import each other
- `allow_adjacent_only = false` -- any higher layer may import any lower layer (not just adjacent)

## 6. AOP Weaving Flow

The MDSOC weaving engine transforms MIR at compile time based on predicate-matched join points.

```
    Source Code                    capsule.sdn / WeavingConfig
    (business logic)               (weaving rules)
         |                              |
         v                              v
    +----------+               +------------------+
    |  Parser  |               | Predicate Parser |
    +----------+               +------------------+
         |                              |
         v                              v
    +----------+               +------------------+
    |   HIR    |               | Join Point Match |
    +----------+               +------------------+
         |                              |
         v                              v
    +----------+     merge     +------------------+
    |   MIR    | <------------ | Advice Insertion |
    +----------+               +------------------+
         |
         v
    +------------------+
    | MIR Optimization |
    +------------------+
         |
         v
    +------------------+
    | Backend Codegen  |
    +------------------+
```

### Advice Insertion Detail

For each function in MIR, the weaving engine:

1. **Evaluates predicates** against the function's module path, name, and annotations.
2. **Sorts matched rules by priority** (higher priority runs first).
3. **Inserts advice code** based on the advice form:

```
Before Advice:
    +-------------------------------------------+
    |  check_auth_before(ctx)                   |  <-- injected
    |  check_capability_before(ctx, cap)        |  <-- injected
    |  validate_request_input(ctx)              |  <-- injected
    |  ---- original function body ----         |
    +-------------------------------------------+

Around Advice:
    +-------------------------------------------+
    |  log_request_advice(ctx, proceed) {       |  <-- wraps
    |      val start = now()                    |
    |      val result = proceed()  // original  |
    |      log_event(...)                       |
    |      result                               |
    |  }                                        |
    +-------------------------------------------+

AfterSuccess Advice:
    +-------------------------------------------+
    |  ---- original function body ----         |
    |  if result is Ok:                         |
    |      log_auth_success_advice(ctx)         |  <-- injected
    +-------------------------------------------+

AfterError Advice:
    +-------------------------------------------+
    |  ---- original function body ----         |
    |  if result is Err(e):                     |
    |      log_auth_failure_advice(ctx, e)      |  <-- injected
    +-------------------------------------------+
```

### Security Aspects Woven by `weavingconfig_with_security_aspects()`

| # | Predicate | Advice Function | Form | Priority |
|---|-----------|----------------|------|----------|
| 1 | `execution(*.handle_request) & within(http_server.**)` | `audit_advice.log_request_advice` | Around | 1000 |
| 2 | `execution(*.authenticate*) \| execution(*.verify_password*)` | `audit_advice.log_auth_success_advice` | AfterSuccess | 900 |
| 3 | `execution(*.authenticate*) \| execution(*.verify_password*)` | `audit_advice.log_auth_failure_advice` | AfterError | 900 |
| 4 | `attr(requires_auth) & within(http_server.**)` | `auth_advice.check_auth_before` | Before | 800 |
| 5 | `execution(*.render_html*) & within(ui.**)` | `validation_advice.sanitize_html_output` | Around | 700 |
| 6 | `attr(validates_input) & within(http_server.**)` | `validation_advice.validate_request_input` | Before | 750 |

## 7. HTTP Middleware Pipeline Position

The 5 security middleware map to 3 phases of the existing nginx-style 7-phase pipeline.

```
    Incoming HTTP Request
            |
            v
    +============================+
    | Phase: PreRead (priority)  |
    |                            |
    |  [100] Rate Limiting       |  <-- Token bucket per peer_addr
    |        reject 429 if over  |      Exempt paths configurable
    |                            |
    +============================+
            |
            v
    +============================+
    | Phase: Read (priority)     |
    |                            |
    |  [90] Request Validation   |  <-- Path traversal, null bytes,
    |       reject 400 if bad    |      header size (8KB), URI size (8KB)
    |                            |
    +============================+
            |
            v
    +============================+
    | Phase: Access (priority)   |
    |                            |
    |  [150] CSRF Protection     |  <-- Double-submit cookie check
    |        reject 403 if fail  |      HMAC-SHA256 tokens
    |                            |
    |  [180] CORS Enforcement    |  <-- Origin allowlist validation
    |        reject 403 if bad   |      Preflight OPTIONS handling
    |                            |
    |  [200] Security Headers    |  <-- CSP, HSTS, X-Frame-Options,
    |        always Continue     |      X-Content-Type-Options,
    |                            |      Referrer-Policy
    +============================+
            |
            v
    +============================+
    | Phase: Content             |
    |   (application handlers)   |
    +============================+
            |
            v
    +============================+
    | Phase: Response            |
    |   apply_security_headers() |  <-- Security headers injected
    +============================+
            |
            v
        HTTP Response
```

## 8. Capability Enforcement Flow

### Default-Deny Policy Resolution

```
    Capability Request (e.g., FileSystemWrite)
            |
            v
    +----------------------------+
    | Is cap in denied list?     |-----> YES: Log CapabilityDenied
    +----------------------------+              Return Err
            | NO
            v
    +----------------------------+
    | Is cap in granted list?    |-----> YES: Return Ok(true)
    +----------------------------+
            | NO
            v
    +----------------------------+
    | default_deny = true?       |-----> YES: Log CapabilityDenied
    +----------------------------+              Return Err
            | NO
            v
        Return Ok(true)
```

### Tauri Backend Enforcement Path

```
    User action (e.g., show notification)
            |
            v
    +-----------------------------------+
    | TauriBackend.show_notification()  |
    +-----------------------------------+
            |
            v
    +-----------------------------------+
    | require_capability(policy,        |
    |     Capability.Notification)      |
    +-----------------------------------+
            |              |
          Ok(true)    Err(NotSupported)
            |              |
            v              v
    +---------------+  +-------------------+
    | Build IPC msg |  | Return Err to     |
    | and print     |  | caller (blocked)  |
    +---------------+  +-------------------+
```

### UISession Gated Surface Open

```
    session.open_surface_gated("editor", tree, Capability.FileSystemRead)
            |
            v
    +-----------------------------------+
    | check_capability(policy,          |
    |     Capability.FileSystemRead)    |
    +-----------------------------------+
            |              |
          Ok(_)        Err(msg)
            |              |
            v              v
    +---------------+  +-------------------+
    | surfaces.open |  | Return Err(msg)   |
    | Return Ok(h)  |  | Surface NOT opened|
    +---------------+  +-------------------+
```

### SDN Config Format

```sdn
window:
    id: main
    default: deny
    granted:
        - Notification
        - FileSystemRead
        - Color
        - Images
    denied:
        - ShellAccess
        - ProcessSpawn
```

Parsed by `parse_capability_config()` into a `CapabilityPolicy` with `default_deny: true`, the granted list, and the denied list. Explicit deny always overrides grant.

## 9. Design Decisions

1. **Pure functions for sanitization.** `sanitize.spl` has zero external dependencies -- all functions are pure text transforms. This enables use from any layer without introducing dependency cycles.

2. **Parallel arrays in RateLimitStore.** Token bucket state uses parallel `[text]`, `[i64]`, `[i64]` arrays rather than a `Map<text, Bucket>` to avoid GC and hash map overhead in the hot path.

3. **Audit via AOP, not direct calls.** Business code has zero `log_security_event` imports. The weaving engine injects audit calls at MIR level, guaranteeing coverage and eliminating forgotten-logging bugs.

4. **IPC validation is structural, not AOP.** Message size/format checks in `protocol.spl` run inline because IPC parsing is a single entry point -- AOP would add complexity without coverage benefit.

5. **SecurityGate join point kind.** Added to `JoinPointKind` to allow future capability-gated join points in the MIR, enabling the weaving engine to recognize and instrument capability checks.

## 10. Cross-References

- Requirement: [doc/02_requirements/feature/security_aop.md](../plan/requirement/security_aop.md)
- Research: [doc/01_research/security_aop_architecture_2026-03-28.md](../research/security_aop_architecture_2026-03-28.md)
- Parser security: [doc/01_research/data_format_parser_security_2026-01-31.md](../research/data_format_parser_security_2026-01-31.md)
- Sandbox strategies: [doc/01_research/sandbox_implementation_strategies.md](../research/sandbox_implementation_strategies.md)
- Tauri requirement: [doc/02_requirements/feature/simple_tauri.md](../plan/requirement/simple_tauri.md)
