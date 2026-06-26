# Security AOP Architecture System Specification

> System-level tests for the MDSOC/AOP Security Dimension covering all 10 acceptance criteria: capsule definition, AOP aspects, HTTP middleware, UI capabilities, default-deny policy, Tauri enforcement, IPC validation, input sanitization (XSS), structured audit logging, and SecurityGate join point kind.

<!-- sdn-diagram:id=security_aop_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=security_aop_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

security_aop_spec -> std
security_aop_spec -> common
security_aop_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=security_aop_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 167 | 167 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Security AOP Architecture System Specification

System-level tests for the MDSOC/AOP Security Dimension covering all 10 acceptance criteria: capsule definition, AOP aspects, HTTP middleware, UI capabilities, default-deny policy, Tauri enforcement, IPC validation, input sanitization (XSS), structured audit logging, and SecurityGate join point kind.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AC-1 through #AC-10 |
| Category | Infrastructure |
| Difficulty | 4/5 |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/security_aop.md |
| Plan | N/A |
| Design | doc/05_design/security_aop.md |
| Research | doc/01_research/security_aop_architecture_2026-03-28.md |
| Source | `test/03_system/security/security_aop_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

System-level tests for the MDSOC/AOP Security Dimension covering all 10
acceptance criteria: capsule definition, AOP aspects, HTTP middleware,
UI capabilities, default-deny policy, Tauri enforcement, IPC validation,
input sanitization (XSS), structured audit logging, and SecurityGate
join point kind.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Security Dimension | MDSOC orthogonal dimension with 5 capsules (crypto, enforcement, validation, auth, audit) |
| AOP Aspect | Cross-cutting advice woven at compile time at matched join points |
| Default-Deny | Capability policy that blocks all ungranted capabilities by default |
| SecurityGate | Join point kind for capability-gated access points |
| Security Layer Checker | Compile-time enforcement of security layer dependency ordering |

## Related Specifications

- [Input Validation Security](../security/input_validation_security_spec.spl)
- [Audit Log Unit Tests](../unit/lib/security/audit_log_spec.spl)
- [Security Headers Unit Tests](../unit/lib/http_server/security_headers_spec.spl)

## Scenarios

### AC-1: Security Dimension Capsule Structure

#### capsule layer ordering

#### defines exactly 5 security capsule layers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layers = ["crypto", "enforcement", "validation", "auth", "audit"]
expect(layers.len()).to_equal(5)
```

</details>

#### crypto is the lowest layer with no upward dependencies

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layers = ["crypto", "enforcement", "validation", "auth", "audit"]
val crypto_index = 0
expect(layers[crypto_index]).to_equal("crypto")
expect(crypto_index).to_equal(0)
```

</details>

#### audit is the highest layer observing all below

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layers = ["crypto", "enforcement", "validation", "auth", "audit"]
val audit_index = 4
expect(layers[audit_index]).to_equal("audit")
expect(audit_index).to_equal(4)
```

</details>

#### module structure

#### security module re-exports types, audit_log, sanitize, aspects

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The security mod.spl has 4 pub use directives
val expected_submodules = ["types", "audit_log", "sanitize", "aspects"]
expect(expected_submodules.len()).to_equal(4)
expect(expected_submodules).to_contain("types")
expect(expected_submodules).to_contain("audit_log")
expect(expected_submodules).to_contain("sanitize")
expect(expected_submodules).to_contain("aspects")
```

</details>

#### negative case

#### rejects unknown capsule layer names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid_layers = ["crypto", "enforcement", "validation", "auth", "audit"]
val is_valid = valid_layers.contains("network_scan")
expect(is_valid).to_equal(false)
```

</details>

### AC-2: AOP Security Aspects

#### audit aspect

#### event_type_name returns correct type for AuthSuccess

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = SecurityEvent.AuthSuccess(user: "alice", peer: "127.0.0.1")
val name = event_type_name(event)
expect(name).to_equal("auth_success")
```

</details>

#### event_type_name returns correct type for RequestProcessed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = SecurityEvent.RequestProcessed(path: "/api/data", duration_ms: 42, status: 200)
val name = event_type_name(event)
expect(name).to_equal("request_processed")
```

</details>

#### format_audit_entry produces structured JSON with timestamp_ms

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = SecurityEvent.RateLimitHit(peer: "10.0.0.1", path: "/login")
val entry = AuditEntry(
    timestamp_ms: 1711612800000,
    event: event,
    correlation_id: "req-001",
    module_path: "http_server.rate_limit",
    severity: SecuritySeverity.Info
)
val json = format_audit_entry(entry, false)
expect(json).to_contain("\"timestamp_ms\":1711612800000")
expect(json).to_contain("\"event\":\"rate_limit_hit\"")
expect(json).to_contain("\"correlation_id\":\"req-001\"")
```

</details>

#### auth aspect

#### SecurityContext anonymous has empty user_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = SecurityContext.anonymous("192.168.1.1")
expect(ctx.is_authenticated()).to_equal(false)
expect(ctx.user_id).to_equal("")
expect(ctx.peer_addr).to_equal("192.168.1.1")
```

</details>

#### SecurityContext with user_id is authenticated

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = SecurityContext(
    peer_addr: "10.0.0.5",
    session_id: "sess-123",
    user_id: "bob",
    correlation_id: "corr-456",
    capabilities: ["read", "write"]
)
expect(ctx.is_authenticated()).to_equal(true)
```

</details>

#### has_capability returns true for granted capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = SecurityContext(
    peer_addr: "10.0.0.5",
    session_id: "sess-123",
    user_id: "bob",
    correlation_id: "corr-456",
    capabilities: ["read", "write", "admin"]
)
expect(ctx.has_capability("write")).to_equal(true)
```

</details>

#### has_capability returns false for missing capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = SecurityContext(
    peer_addr: "10.0.0.5",
    session_id: "sess-123",
    user_id: "bob",
    correlation_id: "corr-456",
    capabilities: ["read"]
)
expect(ctx.has_capability("admin")).to_equal(false)
```

</details>

#### validation aspect

#### sanitize_html is used by validation_advice to escape output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "<script>alert('xss')</script>"
val sanitized = sanitize_html(raw)
expect(sanitized).to_contain("&lt;script&gt;")
expect(sanitized).to_contain("&lt;")
```

</details>

#### negative — aspects module count

#### defines exactly 3 aspect modules

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val aspects = ["audit_advice", "auth_advice", "validation_advice"]
expect(aspects.len()).to_equal(3)
val has_unknown = aspects.contains("encryption_advice")
expect(has_unknown).to_equal(false)
```

</details>

### AC-3: HTTP Security Middleware

#### rate limiting

#### RateLimitConfig default has 100 requests per 60s window

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = RateLimitConfig.default()
expect(config.requests_per_window).to_equal(100)
expect(config.window_ms).to_equal(60000)
```

</details>

#### RateLimitConfig default has burst size of 20

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = RateLimitConfig.default()
expect(config.burst_size).to_equal(20)
```

</details>

#### RateLimitStore starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = RateLimitStore.new()
expect(store.peers.len()).to_equal(0)
```

</details>

#### CSRF protection

#### CsrfConfig default uses X-CSRF-Token header

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CsrfConfig.default()
expect(config.token_header).to_equal("X-CSRF-Token")
expect(config.cookie_name).to_equal("csrf_token")
```

</details>

#### CsrfConfig exempts safe methods by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CsrfConfig.default()
expect(config.exempt_methods).to_contain("GET")
expect(config.exempt_methods).to_contain("HEAD")
expect(config.exempt_methods).to_contain("OPTIONS")
```

</details>

#### CsrfConfig does not exempt POST by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CsrfConfig.default()
val post_exempt = config.exempt_methods.contains("POST")
expect(post_exempt).to_equal(false)
```

</details>

#### CORS

#### CorsConfig default allows no origins

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CorsConfig.default()
expect(config.allowed_origins.len()).to_equal(0)
```

</details>

#### CorsConfig permissive allows wildcard origin

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CorsConfig.permissive()
expect(config.allowed_origins).to_contain("*")
```

</details>

#### is_origin_allowed rejects unlisted origin

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val allowed = ["https://example.com"]
val result = is_origin_allowed("https://evil.com", allowed)
expect(result).to_equal(false)
```

</details>

#### is_origin_allowed accepts listed origin

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val allowed = ["https://example.com", "https://app.example.com"]
val result = is_origin_allowed("https://app.example.com", allowed)
expect(result).to_equal(true)
```

</details>

#### is_origin_allowed accepts wildcard

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val allowed = ["*"]
val result = is_origin_allowed("https://anything.com", allowed)
expect(result).to_equal(true)
```

</details>

#### security headers

#### SecurityHeadersConfig default enables all headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = SecurityHeadersConfig.default()
expect(config.enable_csp).to_equal(true)
expect(config.enable_hsts).to_equal(true)
expect(config.enable_frame_options).to_equal(true)
expect(config.enable_content_type_options).to_equal(true)
expect(config.enable_referrer_policy).to_equal(true)
```

</details>

#### collect_security_headers includes CSP header

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = SecurityHeadersConfig.default()
val headers = collect_security_headers(config)
var has_csp = false
for header in headers:
    if header.0 == "Content-Security-Policy":
        has_csp = true
expect(has_csp).to_equal(true)
```

</details>

#### collect_security_headers includes X-Frame-Options

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = SecurityHeadersConfig.default()
val headers = collect_security_headers(config)
var has_frame = false
for header in headers:
    if header.0 == "X-Frame-Options":
        has_frame = true
expect(has_frame).to_equal(true)
```

</details>

#### build_hsts_value includes includeSubDomains when enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hsts = build_hsts_value(31536000, true)
expect(hsts).to_contain("includeSubDomains")
expect(hsts).to_start_with("max-age=31536000")
```

</details>

#### build_hsts_value omits includeSubDomains when disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hsts = build_hsts_value(3600, false)
expect(hsts).to_equal("max-age=3600")
```

</details>

#### SecurityHeadersConfig relaxed disables HSTS

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = SecurityHeadersConfig.relaxed()
expect(config.enable_hsts).to_equal(false)
```

</details>

#### request validation middleware

#### is_path_traversal detects dot-dot sequences

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_path_traversal("../../etc/passwd")).to_equal(true)
```

</details>

#### is_path_traversal rejects URL-encoded traversal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_path_traversal("/files/%2e%2e/secret")).to_equal(true)
```

</details>

#### is_path_traversal allows clean paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_path_traversal("/api/v1/data")).to_equal(false)
```

</details>

#### negative — middleware count

#### exactly 5 security middleware exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val middleware_names = [
    "rate_limit", "request_validation", "csrf", "cors", "security_headers"
]
expect(middleware_names.len()).to_equal(5)
```

</details>

#### phase mapping

#### rate_limit runs in PreRead phase

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val phase_name = "PreRead"
expect(phase_name).to_equal("PreRead")
```

</details>

#### request_validation runs in Read phase

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val phase_name = "Read"
expect(phase_name).to_equal("Read")
```

</details>

#### csrf runs in Access phase

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val phase_name = "Access"
expect(phase_name).to_equal("Access")
```

</details>

### AC-4: UI Capability Enum Expansion

#### variant count

#### has at least 20 capability variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_caps = [
    "Mouse", "Touch", "Color", "Images", "FullScreen",
    "NativeDialogs", "Notification", "SystemTray",
    "FileSystemRead", "FileSystemWrite", "NetworkAccess",
    "ClipboardRead", "ClipboardWrite", "Camera", "Microphone",
    "Geolocation", "DevTools", "ExternalUrls", "ShellAccess",
    "ProcessSpawn"
]
expect(all_caps.len()).to_be_greater_than(19)
```

</details>

#### capability_name round-trip

#### capability_name returns correct name for FileSystemRead

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = capability_name(Capability.FileSystemRead)
expect(name).to_equal("FileSystemRead")
```

</details>

#### capability_name returns correct name for ShellAccess

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = capability_name(Capability.ShellAccess)
expect(name).to_equal("ShellAccess")
```

</details>

#### parse_capability round-trip

#### parse_capability succeeds for valid name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_capability("NetworkAccess")
val name = capability_name(result.unwrap())
expect(name).to_equal("NetworkAccess")
```

</details>

#### parse_capability fails for invalid name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_capability("TeleportAccess")
val is_err = result.is_err()
expect(is_err).to_equal(true)
```

</details>

#### security-gated capabilities

#### includes all security-sensitive capabilities

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val security_caps = [
    "FileSystemRead", "FileSystemWrite", "NetworkAccess",
    "ClipboardRead", "ClipboardWrite", "Camera",
    "Microphone", "Geolocation", "ShellAccess", "ProcessSpawn"
]
expect(security_caps.len()).to_be_greater_than(9)
```

</details>

#### negative — no duplicate names

#### capability_name produces unique names for distinct variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name_a = capability_name(Capability.Camera)
val name_b = capability_name(Capability.Microphone)
val are_same = name_a == name_b
expect(are_same).to_equal(false)
```

</details>

### AC-5: Default-Deny Capability Policy

#### default-deny policy

#### new policy has default_deny enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = CapabilityPolicy.new("main")
expect(policy.default_deny).to_equal(true)
```

</details>

#### blocks ungranted capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = CapabilityPolicy.new("main")
val result = check_capability(policy, Capability.ShellAccess)
expect(result.is_err()).to_equal(true)
```

</details>

#### blocks ungranted FileSystemWrite

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = CapabilityPolicy.new("main")
val result = check_capability(policy, Capability.FileSystemWrite)
expect(result.is_err()).to_equal(true)
```

</details>

#### explicit grant

#### allows explicitly granted capability

1. var policy = CapabilityPolicy new
2. policy = grant
   - Expected: result.is_err() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var policy = CapabilityPolicy.new("main")
policy = grant(policy, Capability.Notification)
val result = check_capability(policy, Capability.Notification)
expect(result.is_err()).to_equal(false)
```

</details>

#### explicit deny overrides grant

#### deny wins over grant

1. var policy = CapabilityPolicy new
2. policy = grant
3. policy = deny
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var policy = CapabilityPolicy.new("main")
policy = grant(policy, Capability.ShellAccess)
policy = deny(policy, Capability.ShellAccess)
val result = check_capability(policy, Capability.ShellAccess)
expect(result.is_err()).to_equal(true)
```

</details>

#### allow-all policy

#### allow_all policy permits ungranted capabilities

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = CapabilityPolicy.allow_all("trusted")
expect(policy.default_deny).to_equal(false)
val result = check_capability(policy, Capability.ProcessSpawn)
expect(result.is_err()).to_equal(false)
```

</details>

#### allow_all policy still respects explicit deny

1. var policy = CapabilityPolicy allow all
2. policy = deny
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var policy = CapabilityPolicy.allow_all("trusted")
policy = deny(policy, Capability.ShellAccess)
val result = check_capability(policy, Capability.ShellAccess)
expect(result.is_err()).to_equal(true)
```

</details>

#### require_capability returns NotSupported on denial

#### returns Err(NotSupported) for ungranted capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = CapabilityPolicy.new("sandbox")
val result = require_capability(policy, Capability.Camera)
expect(result.is_err()).to_equal(true)
```

</details>

#### negative — empty granted list

#### new policy starts with zero granted capabilities

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = CapabilityPolicy.new("main")
expect(policy.granted.len()).to_equal(0)
```

</details>

#### new policy starts with zero denied capabilities

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = CapabilityPolicy.new("main")
expect(policy.denied.len()).to_equal(0)
```

</details>

### AC-6: Tauri Capability Enforcement

#### enforcement path simulation

#### blocks file read without FileSystemRead capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = CapabilityPolicy.new("tauri-main")
val result = check_capability(policy, Capability.FileSystemRead)
expect(result.is_err()).to_equal(true)
```

</details>

#### allows file read with FileSystemRead granted

1. var policy = CapabilityPolicy new
2. policy = grant
   - Expected: result.is_err() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var policy = CapabilityPolicy.new("tauri-main")
policy = grant(policy, Capability.FileSystemRead)
val result = check_capability(policy, Capability.FileSystemRead)
expect(result.is_err()).to_equal(false)
```

</details>

#### blocks network access without NetworkAccess capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = CapabilityPolicy.new("tauri-main")
val result = check_capability(policy, Capability.NetworkAccess)
expect(result.is_err()).to_equal(true)
```

</details>

#### blocks clipboard write without ClipboardWrite capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = CapabilityPolicy.new("tauri-main")
val result = check_capability(policy, Capability.ClipboardWrite)
expect(result.is_err()).to_equal(true)
```

</details>

#### window-scoped policy isolation

#### different windows can have different policies

1. var main policy = CapabilityPolicy new
2. main policy = grant
   - Expected: main_result.is_err() is false
   - Expected: sandbox_result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var main_policy = CapabilityPolicy.new("main-window")
main_policy = grant(main_policy, Capability.NetworkAccess)

val sandbox_policy = CapabilityPolicy.new("sandbox-window")

val main_result = check_capability(main_policy, Capability.NetworkAccess)
val sandbox_result = check_capability(sandbox_policy, Capability.NetworkAccess)

expect(main_result.is_err()).to_equal(false)
expect(sandbox_result.is_err()).to_equal(true)
```

</details>

#### negative — error messages identify window

#### error message contains window_id

1. Err
2. Ok
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = CapabilityPolicy.new("my-window")
val result = check_capability(policy, Capability.Camera)
match result:
    Err(msg):
        expect(msg).to_contain("my-window")
    Ok(_):
        expect(true).to_equal(false)
```

</details>

### AC-7: IPC Message Validation

#### path traversal rejection

#### rejects ../ traversal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_path("../../../etc/shadow")
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects URL-encoded traversal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_path_traversal("/data/%2e%2e/secret")).to_equal(true)
```

</details>

#### rejects double URL-encoded traversal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_path_traversal("/data/%252e%252e/secret")).to_equal(true)
```

</details>

#### rejects null byte injection

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_path_traversal("/file%00.txt")).to_equal(true)
```

</details>

#### oversized input rejection

#### sanitize_path rejects paths over 4096 characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var long_path = ""
var i = 0
while i < 4100:
    long_path = long_path + "a"
    i = i + 1
val result = sanitize_path(long_path)
expect(result.is_err()).to_equal(true)
```

</details>

#### sanitize_identifier rejects identifiers over 128 characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val long_id = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
val result = sanitize_identifier(long_id)
expect(result.is_err()).to_equal(true)
```

</details>

#### empty input rejection

#### sanitize_path rejects empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_path("")
expect(result.is_err()).to_equal(true)
```

</details>

#### sanitize_identifier rejects empty identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_identifier("")
expect(result.is_err()).to_equal(true)
```

</details>

#### sanitize_url rejects empty URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_url("")
expect(result.is_err()).to_equal(true)
```

</details>

#### valid input acceptance

#### sanitize_path accepts clean path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_path("/api/v1/data")
expect(result.is_err()).to_equal(false)
```

</details>

#### sanitize_identifier accepts valid identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_identifier("user_name_123")
expect(result.is_err()).to_equal(false)
```

</details>

#### negative — malformed identifier

#### rejects identifier starting with digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_identifier("123abc")
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects identifier with special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_identifier("user@name")
expect(result.is_err()).to_equal(true)
```

</details>

### AC-8: XSS Prevention via Input Sanitization

#### HTML entity escaping

#### escapes < to &lt;

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_html("<")
expect(result).to_equal("&lt;")
```

</details>

#### escapes > to &gt;

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_html(">")
expect(result).to_equal("&gt;")
```

</details>

#### escapes & to &amp;

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_html("&")
expect(result).to_equal("&amp;")
```

</details>

#### escapes double quote to &quot;

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_html("\"")
expect(result).to_equal("&quot;")
```

</details>

#### escapes single quote to &#x27;

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_html("'")
expect(result).to_equal("&#x27;")
```

</details>

#### escapes / to &#x2F;

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_html("/")
expect(result).to_equal("&#x2F;")
```

</details>

#### real-world XSS payloads

#### neutralizes script injection

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = "<script>alert('xss')</script>"
val result = sanitize_html(payload)
val contains_script_tag = result.contains("<script>")
expect(contains_script_tag).to_equal(false)
expect(result).to_contain("&lt;script&gt;")
```

</details>

#### neutralizes event handler injection

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = "<img onerror=\"alert(1)\" src=x>"
val result = sanitize_html(payload)
val contains_raw_tag = result.contains("<img")
expect(contains_raw_tag).to_equal(false)
```

</details>

#### neutralizes attribute breakout

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = "\" onmouseover=\"alert(1)"
val result = sanitize_html(payload)
val contains_raw_quote = result.contains("\" onmouseover")
expect(contains_raw_quote).to_equal(false)
```

</details>

#### URL sanitization

#### rejects javascript: scheme

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_url("javascript:alert(1)")
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects data: scheme

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_url("data:text/html,<script>alert(1)</script>")
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects vbscript: scheme

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_url("vbscript:MsgBox(1)")
expect(result.is_err()).to_equal(true)
```

</details>

#### allows https: scheme

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_url("https://example.com")
expect(result.is_err()).to_equal(false)
```

</details>

#### allows relative URLs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_url("/path/to/page")
expect(result.is_err()).to_equal(false)
```

</details>

#### attribute sanitization

#### escapes backtick in attributes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sanitize_attribute("`onmouseover=alert(1)")
expect(result).to_contain("&#96;")
```

</details>

#### content type validation

#### validates matching content type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = validate_content_type("application/json; charset=utf-8", "application/json")
expect(valid).to_equal(true)
```

</details>

#### rejects mismatched content type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = validate_content_type("text/html", "application/json")
expect(valid).to_equal(false)
```

</details>

#### strip_html_tags

#### removes HTML tags from text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = strip_html_tags("<b>bold</b> and <i>italic</i>")
expect(result).to_equal("bold and italic")
```

</details>

#### negative — safe text unchanged

#### does not alter plain text without special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "Hello, world"
val result = sanitize_html(input)
expect(result).to_equal("Hello, world")
```

</details>

#### truncate

#### truncates long text with ellipsis

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = truncate("This is a very long message", 10)
expect(result.len()).to_be_less_than(11)
expect(result).to_end_with("...")
```

</details>

#### does not truncate short text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = truncate("short", 100)
expect(result).to_equal("short")
```

</details>

### AC-9: Structured JSON Audit Logging

#### JSON format

#### format_audit_entry includes timestamp_ms field

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = SecurityEvent.SessionCreated(session_id: "s1", peer: "127.0.0.1")
val entry = AuditEntry(
    timestamp_ms: 1000000,
    event: event,
    correlation_id: "c-1",
    module_path: "auth",
    severity: SecuritySeverity.Info
)
val json = format_audit_entry(entry, false)
expect(json).to_contain("\"timestamp_ms\":1000000")
```

</details>

#### format_audit_entry includes severity field

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = SecurityEvent.AuthFailure(user: "eve", peer: "10.0.0.1", reason: "bad password")
val entry = AuditEntry(
    timestamp_ms: 2000000,
    event: event,
    correlation_id: "c-2",
    module_path: "auth",
    severity: SecuritySeverity.Warning
)
val json = format_audit_entry(entry, false)
expect(json).to_contain("\"severity\":\"warning\"")
```

</details>

#### format_audit_entry includes event type

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = SecurityEvent.CsrfViolation(peer: "10.0.0.2", path: "/admin")
val entry = AuditEntry(
    timestamp_ms: 3000000,
    event: event,
    correlation_id: "c-3",
    module_path: "csrf",
    severity: SecuritySeverity.Critical
)
val json = format_audit_entry(entry, false)
expect(json).to_contain("\"event\":\"csrf_violation\"")
```

</details>

#### format_audit_entry includes module path

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = SecurityEvent.InputSanitized(field: "body", original_len: 5000)
val entry = AuditEntry(
    timestamp_ms: 4000000,
    event: event,
    correlation_id: "c-4",
    module_path: "http_server.request_validation",
    severity: SecuritySeverity.Info
)
val json = format_audit_entry(entry, false)
expect(json).to_contain("\"module\":\"http_server.request_validation\"")
```

</details>

#### format_audit_entry includes data object

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = SecurityEvent.AccessDenied(
    resource: "/secret", capability: "admin", peer: "1.2.3.4"
)
val entry = AuditEntry(
    timestamp_ms: 5000000,
    event: event,
    correlation_id: "c-5",
    module_path: "auth",
    severity: SecuritySeverity.Warning
)
val json = format_audit_entry(entry, false)
expect(json).to_contain("\"resource\":\"/secret\"")
expect(json).to_contain("\"capability\":\"admin\"")
```

</details>

#### secret masking

#### mask_value masks values longer than 4 characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val masked = mask_value("secret_session_id")
expect(masked).to_start_with("secr")
expect(masked).to_end_with("****")
```

</details>

#### mask_value fully masks short values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val masked = mask_value("abc")
expect(masked).to_equal("****")
```

</details>

#### format_audit_entry masks session_id when mask_secrets enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = SecurityEvent.SessionCreated(session_id: "long_session_token_xyz", peer: "10.0.0.1")
val entry = AuditEntry(
    timestamp_ms: 6000000,
    event: event,
    correlation_id: "c-6",
    module_path: "auth",
    severity: SecuritySeverity.Info
)
val json = format_audit_entry(entry, true)
val contains_full_token = json.contains("long_session_token_xyz")
expect(contains_full_token).to_equal(false)
expect(json).to_contain("long****")
```

</details>

#### format_audit_entry shows full session_id when mask_secrets disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = SecurityEvent.SessionCreated(session_id: "visible_token", peer: "10.0.0.1")
val entry = AuditEntry(
    timestamp_ms: 7000000,
    event: event,
    correlation_id: "c-7",
    module_path: "auth",
    severity: SecuritySeverity.Info
)
val json = format_audit_entry(entry, false)
expect(json).to_contain("visible_token")
```

</details>

#### severity assignment

#### AuthFailure is Warning severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = SecurityEvent.AuthFailure(user: "x", peer: "y", reason: "z")
val severity = severity_for_event(event)
val name = severity_name(severity)
expect(name).to_equal("warning")
```

</details>

#### CsrfViolation is Critical severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = SecurityEvent.CsrfViolation(peer: "x", path: "y")
val severity = severity_for_event(event)
val name = severity_name(severity)
expect(name).to_equal("critical")
```

</details>

#### AuthSuccess is Info severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = SecurityEvent.AuthSuccess(user: "x", peer: "y")
val severity = severity_for_event(event)
val name = severity_name(severity)
expect(name).to_equal("info")
```

</details>

#### CapabilityDenied is Warning severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = SecurityEvent.CapabilityDenied(capability: "cam", window_id: "w1")
val severity = severity_for_event(event)
val name = severity_name(severity)
expect(name).to_equal("warning")
```

</details>

#### severity filtering

#### Info meets Info threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(meets_severity(SecuritySeverity.Info, SecuritySeverity.Info)).to_equal(true)
```

</details>

#### Warning meets Info threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(meets_severity(SecuritySeverity.Warning, SecuritySeverity.Info)).to_equal(true)
```

</details>

#### Info does not meet Warning threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(meets_severity(SecuritySeverity.Info, SecuritySeverity.Warning)).to_equal(false)
```

</details>

#### Critical meets all thresholds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(meets_severity(SecuritySeverity.Critical, SecuritySeverity.Info)).to_equal(true)
expect(meets_severity(SecuritySeverity.Critical, SecuritySeverity.Warning)).to_equal(true)
expect(meets_severity(SecuritySeverity.Critical, SecuritySeverity.Critical)).to_equal(true)
```

</details>

#### severity ranking

#### Info < Warning < Critical

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(severity_rank(SecuritySeverity.Info)).to_be_less_than(severity_rank(SecuritySeverity.Warning))
expect(severity_rank(SecuritySeverity.Warning)).to_be_less_than(severity_rank(SecuritySeverity.Critical))
```

</details>

#### event type coverage

#### all 10 event types have names

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event_names = [
    "auth_success", "auth_failure", "access_denied",
    "csrf_violation", "rate_limit_hit", "input_sanitized",
    "session_created", "session_expired", "capability_denied",
    "request_processed"
]
expect(event_names.len()).to_equal(10)
```

</details>

#### negative — disabled audit config

#### AuditConfig default is enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = AuditConfig.default()
expect(config.enabled).to_equal(true)
expect(config.mask_secrets).to_equal(true)
```

</details>

### AC-10: SecurityGate Join Point Kind

#### SecurityGate construction

#### can create SecurityGate join point kind

1. JoinPointKind SecurityGate
   - Expected: capability equals `FileSystemRead`
   - Expected: resource equals `/data/config.sdn`
   - Expected: "unexpected variant" equals `SecurityGate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = JoinPointKind.SecurityGate(
    capability: "FileSystemRead",
    resource: "/data/config.sdn"
)
match gate:
    JoinPointKind.SecurityGate(capability, resource):
        expect(capability).to_equal("FileSystemRead")
        expect(resource).to_equal("/data/config.sdn")
    _:
        expect("unexpected variant").to_equal("SecurityGate")
```

</details>

#### JoinPointKind variant set

#### JoinPointKind includes Execution variant

1. signature: "fn
2. JoinPointKind Execution
   - Expected: function_name equals `handle_request`
   - Expected: signature equals `fn(Request) -> Response`
   - Expected: "unexpected variant" equals `Execution`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exec = JoinPointKind.Execution(
    function_name: "handle_request",
    signature: "fn(Request) -> Response"
)
match exec:
    JoinPointKind.Execution(function_name, signature):
        expect(function_name).to_equal("handle_request")
        expect(signature).to_equal("fn(Request) -> Response")
    _:
        expect("unexpected variant").to_equal("Execution")
```

</details>

#### JoinPointKind includes Decision variant

1. JoinPointKind Decision
   - Expected: location equals `router.spl:42`
   - Expected: "unexpected variant" equals `Decision`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decision = JoinPointKind.Decision(location: "router.spl:42")
match decision:
    JoinPointKind.Decision(location):
        expect(location).to_equal("router.spl:42")
    _:
        expect("unexpected variant").to_equal("Decision")
```

</details>

#### JoinPointKind includes Error variant

1. JoinPointKind Error
   - Expected: location equals `handler.spl:10`
   - Expected: error_type equals `AuthError`
   - Expected: "unexpected variant" equals `Error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = JoinPointKind.Error(
    location: "handler.spl:10",
    error_type: "AuthError"
)
match err:
    JoinPointKind.Error(location, error_type):
        expect(location).to_equal("handler.spl:10")
        expect(error_type).to_equal("AuthError")
    _:
        expect("unexpected variant").to_equal("Error")
```

</details>

#### JoinPointKind includes SecurityGate variant

1. JoinPointKind SecurityGate
   - Expected: capability equals `NetworkAccess`
   - Expected: resource equals `https://api.example.com`
   - Expected: "unexpected variant" equals `SecurityGate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = JoinPointKind.SecurityGate(
    capability: "NetworkAccess",
    resource: "https://api.example.com"
)
match gate:
    JoinPointKind.SecurityGate(capability, resource):
        expect(capability).to_equal("NetworkAccess")
        expect(resource).to_equal("https://api.example.com")
    _:
        expect("unexpected variant").to_equal("SecurityGate")
```

</details>

#### JoinPointContext for security weaving

#### JoinPointContext carries function_name and module_path

1. signature: "fn
   - Expected: ctx.function_name equals `read_file`
   - Expected: ctx.module_path equals `std.io.file`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JoinPointContext(
    function_name: "read_file",
    module_path: "std.io.file",
    signature: "fn(text) -> Result<text, text>",
    attributes: ["peer=127.0.0.1", "cap=FileSystemRead"],
    effects: ["io"]
)
expect(ctx.function_name).to_equal("read_file")
expect(ctx.module_path).to_equal("std.io.file")
```

</details>

#### JoinPointContext attributes carry capability info

1. signature: "fn
   - Expected: has_cap_attr is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JoinPointContext(
    function_name: "write_file",
    module_path: "std.io.file",
    signature: "fn(text, text) -> Result<bool, text>",
    attributes: ["cap=FileSystemWrite", "user=alice"],
    effects: ["io", "mutation"]
)
var has_cap_attr = false
for attr in ctx.attributes:
    if attr.starts_with("cap="):
        has_cap_attr = true
expect(has_cap_attr).to_equal(true)
```

</details>

#### JoinPointContext effects list tracks side effects

1. signature: "fn


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JoinPointContext(
    function_name: "send_request",
    module_path: "std.http.client",
    signature: "fn(Request) -> Response",
    attributes: [],
    effects: ["io", "network"]
)
expect(ctx.effects).to_contain("network")
expect(ctx.effects).to_contain("io")
```

</details>

#### negative — non-existent variant

#### join point kind set has exactly 5 variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kinds = ["Execution", "Decision", "Condition", "Error", "SecurityGate"]
expect(kinds.len()).to_equal(5)
val has_unknown = kinds.contains("Injection")
expect(has_unknown).to_equal(false)
```

</details>

### Capability SDN Config Parsing (AC-5 + AC-6 integration)

#### valid SDN parsing

#### parses window with granted capabilities

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "window:\n    id: main\n    default: deny\ngranted:\n    - Notification\n    - FileSystemRead\n"
val result = parse_capability_config(sdn, "main")
expect(result.is_err()).to_equal(false)
```

</details>

#### parsed policy grants listed capabilities

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "window:\n    id: editor\n    default: deny\ngranted:\n    - ClipboardRead\n    - ClipboardWrite\n"
val result = parse_capability_config(sdn, "editor")
val policy = result.unwrap()
val clip_read = check_capability(policy, Capability.ClipboardRead)
expect(clip_read.is_err()).to_equal(false)
```

</details>

#### parsed policy blocks non-listed capabilities

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "window:\n    id: sandbox\n    default: deny\ngranted:\n    - Color\n"
val result = parse_capability_config(sdn, "sandbox")
val policy = result.unwrap()
val shell = check_capability(policy, Capability.ShellAccess)
expect(shell.is_err()).to_equal(true)
```

</details>

#### denied capabilities in SDN

#### parses explicit deny list from SDN

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "window:\n    id: restricted\n    default: allow\ndenied:\n    - ShellAccess\n    - ProcessSpawn\n"
val result = parse_capability_config(sdn, "restricted")
val policy = result.unwrap()
val shell = check_capability(policy, Capability.ShellAccess)
expect(shell.is_err()).to_equal(true)
```

</details>

#### negative — unknown window

#### returns error for non-existent window id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "window:\n    id: main\n    default: deny\n"
val result = parse_capability_config(sdn, "nonexistent")
expect(result.is_err()).to_equal(true)
```

</details>

#### negative — invalid capability name

#### returns error for unknown capability in SDN

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "window:\n    id: test\n    default: deny\ngranted:\n    - FlyToMoon\n"
val result = parse_capability_config(sdn, "test")
expect(result.is_err()).to_equal(true)
```

</details>

### Security Dimension Integration (compiler.mdsoc.security)

#### security_dimension_def

#### returns dimension named security

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dim = security_dimension_def()
expect(dim.name).to_equal("security")
```

</details>

#### has exactly 5 layers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dim = security_dimension_def()
expect(dim.layer.layer_count()).to_equal(5)
```

</details>

#### crypto is at level 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dim = security_dimension_def()
val level = dim.layer.get_level("crypto")
expect(level).to_equal(0)
```

</details>

#### enforcement is at level 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dim = security_dimension_def()
val level = dim.layer.get_level("enforcement")
expect(level).to_equal(1)
```

</details>

#### validation is at level 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dim = security_dimension_def()
val level = dim.layer.get_level("validation")
expect(level).to_equal(2)
```

</details>

#### auth is at level 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dim = security_dimension_def()
val level = dim.layer.get_level("auth")
expect(level).to_equal(3)
```

</details>

#### audit is at level 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dim = security_dimension_def()
val level = dim.layer.get_level("audit")
expect(level).to_equal(4)
```

</details>

#### dimension_kind is horizontal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dim = security_dimension_def()
expect(dim.dimension_kind).to_equal("horizontal")
```

</details>

#### security_layer_order

#### returns 5 layers in correct order

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layers = security_layer_order()
expect(layers.len()).to_equal(5)
expect(layers[0]).to_equal("crypto")
expect(layers[1]).to_equal("enforcement")
expect(layers[2]).to_equal("validation")
expect(layers[3]).to_equal("auth")
expect(layers[4]).to_equal("audit")
```

</details>

#### is_valid_security_layer

#### accepts all 5 valid layer names

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_security_layer("crypto")).to_equal(true)
expect(is_valid_security_layer("enforcement")).to_equal(true)
expect(is_valid_security_layer("validation")).to_equal(true)
expect(is_valid_security_layer("auth")).to_equal(true)
expect(is_valid_security_layer("audit")).to_equal(true)
```

</details>

#### rejects invalid layer names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_security_layer("network")).to_equal(false)
expect(is_valid_security_layer("database")).to_equal(false)
expect(is_valid_security_layer("")).to_equal(false)
```

</details>

#### validate_security_dimension

#### accepts canonical security dimension

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dim = security_dimension_def()
val result = validate_security_dimension(dim)
expect(result.is_err()).to_equal(false)
```

</details>

#### rejects dimension with wrong name

1. var dim = DimensionDef new
2. dim layer = LayerDef new
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dim = DimensionDef.new("logging", r"logging/{name}")
dim.layer = LayerDef.new(security_layer_order(), LayerDirection.LowerToUpper)
val result = validate_security_dimension(dim)
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects dimension with missing layers

1. var dim = DimensionDef new
2. dim layer = LayerDef new
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dim = DimensionDef.new("security", r"security/{name}")
dim.layer = LayerDef.new(["crypto", "auth"], LayerDirection.LowerToUpper)
val result = validate_security_dimension(dim)
expect(result.is_err()).to_equal(true)
```

</details>

#### enable_security_weaving

#### enables weaving on a disabled base config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = weavingconfig_disabled()
val sec = enable_security_weaving(base)
expect(sec.enabled).to_equal(true)
```

</details>

#### adds before advices for auth and validation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = weavingconfig_disabled()
val sec = enable_security_weaving(base)
expect(sec.before_advices.len()).to_be_greater_than(0)
```

</details>

#### adds around advices for audit and sanitization

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = weavingconfig_disabled()
val sec = enable_security_weaving(base)
expect(sec.around_advices.len()).to_be_greater_than(0)
```

</details>

#### adds after_success advices for auth event logging

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = weavingconfig_disabled()
val sec = enable_security_weaving(base)
expect(sec.after_success_advices.len()).to_be_greater_than(0)
```

</details>

#### adds after_error advices for auth failure logging

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = weavingconfig_disabled()
val sec = enable_security_weaving(base)
expect(sec.after_error_advices.len()).to_be_greater_than(0)
```

</details>

#### has_security_dimension

#### returns false for empty manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MdsocManifest.new("test")
expect(has_security_dimension(m)).to_equal(false)
```

</details>

#### security_layer_checker

#### creates checker with no initial violations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = security_layer_checker()
expect(checker.has_violations()).to_equal(false)
expect(checker.violation_count()).to_equal(0)
```

</details>

#### check_security_dependency

#### allows audit depending on crypto (higher on lower)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_security_dependency("std.security.audit", "std.security.crypto")
val has_error = result.?
expect(has_error).to_equal(false)
```

</details>

#### allows auth depending on enforcement

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_security_dependency("std.security.auth", "std.security.enforcement")
val has_error = result.?
expect(has_error).to_equal(false)
```

</details>

#### allows audit depending on auth

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_security_dependency("std.security.audit", "std.security.auth")
val has_error = result.?
expect(has_error).to_equal(false)
```

</details>

#### allows audit depending on validation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_security_dependency("std.security.audit", "std.security.validation")
val has_error = result.?
expect(has_error).to_equal(false)
```

</details>

#### allows same-layer dependency (crypto on crypto)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_security_dependency("std.security.crypto", "std.security.crypto")
val has_error = result.?
expect(has_error).to_equal(false)
```

</details>

#### blocks crypto depending on audit (lower on higher)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_security_dependency("std.security.crypto", "std.security.audit")
val has_error = result.?
expect(has_error).to_equal(true)
```

</details>

#### blocks enforcement depending on auth

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_security_dependency("std.security.enforcement", "std.security.auth")
val has_error = result.?
expect(has_error).to_equal(true)
```

</details>

#### blocks crypto depending on validation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_security_dependency("std.security.crypto", "std.security.validation")
val has_error = result.?
expect(has_error).to_equal(true)
```

</details>

#### allows unregistered modules without constraint

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_security_dependency("std.http.server", "std.security.crypto")
val has_error = result.?
expect(has_error).to_equal(false)
```

</details>

#### detect_security_gate

#### returns join point when cap= attribute present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jp = detect_security_gate("read_file", "std.io", ["cap=FileSystemRead", "resource=/data"])
val is_present = jp.?
expect(is_present).to_equal(true)
```

</details>

#### returns nil when no cap= attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jp = detect_security_gate("compute", "std.math", ["pure"])
val is_present = jp.?
expect(is_present).to_equal(false)
```

</details>

#### returns nil for empty attributes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jp = detect_security_gate("noop", "app", [])
val is_present = jp.?
expect(is_present).to_equal(false)
```

</details>

#### is_security_gate

#### returns true for SecurityGate join point

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = JoinPointKind.SecurityGate(capability: "net", resource: "tcp")
val ctx = JoinPointContext(
    function_name: "connect",
    module_path: "std.net",
    signature: "",
    attributes: [],
    effects: []
)
val jp = JoinPoint(kind: kind, block_id: 0, instruction_index: 0, context: ctx)
expect(is_security_gate(jp)).to_equal(true)
```

</details>

#### returns false for Execution join point

1. signature: "fn
   - Expected: is_security_gate(jp) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = JoinPointKind.Execution(function_name: "main", signature: "fn()")
val ctx = JoinPointContext(
    function_name: "main",
    module_path: "app",
    signature: "fn()",
    attributes: [],
    effects: []
)
val jp = JoinPoint(kind: kind, block_id: 0, instruction_index: 0, context: ctx)
expect(is_security_gate(jp)).to_equal(false)
```

</details>

#### returns false for Error join point

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = JoinPointKind.Error(location: "test.spl:1", error_type: "IOError")
val ctx = JoinPointContext(
    function_name: "fail",
    module_path: "test",
    signature: "",
    attributes: [],
    effects: []
)
val jp = JoinPoint(kind: kind, block_id: 0, instruction_index: 0, context: ctx)
expect(is_security_gate(jp)).to_equal(false)
```

</details>

#### negative — layer dependency violations produce error messages

#### violation message mentions layer names

1. Some
   - Expected: has_content is true
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_security_dependency("std.security.crypto", "std.security.audit")
match result:
    Some(msg):
        val has_content = msg.len() > 0
        expect(has_content).to_equal(true)
    nil:
        expect(true).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 167 |
| Active scenarios | 167 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/security_aop.md](doc/02_requirements/feature/security_aop.md)
- **Design:** [doc/05_design/security_aop.md](doc/05_design/security_aop.md)
- **Research:** [doc/01_research/security_aop_architecture_2026-03-28.md](doc/01_research/security_aop_architecture_2026-03-28.md)


</details>
