# Remote Security Lifecycle Specification

> 1. var key ring = RemoteSecuritySigningKeyRing new

<!-- sdn-diagram:id=remote_security_lifecycle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=remote_security_lifecycle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

remote_security_lifecycle_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=remote_security_lifecycle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Remote Security Lifecycle Specification

## Scenarios

### remote security lifecycle

#### validates rotated key tokens through persistent session lookup

1. var key ring = RemoteSecuritySigningKeyRing new
2. key ring rotate key
3. var sessions = RemoteSecuritySessionStore new
4. sessions create session
   - Expected: ctx.is_authenticated() is true
   - Expected: ctx.user_id equals `user-1`
   - Expected: ctx.has_capability("profile.read") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key_ring = RemoteSecuritySigningKeyRing.new("k1", "old-secret")
key_ring.rotate_key("k2", "new-secret")

var sessions = RemoteSecuritySessionStore.new()
sessions.create_session("session-1", "user-1", ["profile.read"], 3000)

val token = sign_remote_security_token_with_key_ring(key_ring, "session-1", "user-1", 2500, ["profile.read"])
val headers = RemoteSecurityContextHeaders(
    authorization: "Bearer {token}",
    traceparent: "",
    tenant_id: "",
    policy_version: "",
    request_class: ""
)

val ctx = validate_remote_security_context_with_key_ring(headers, "198.51.100.20", "session-1", key_ring, sessions, 2000)
expect(ctx.is_authenticated()).to_equal(true)
expect(ctx.user_id).to_equal("user-1")
expect(ctx.has_capability("profile.read")).to_equal(true)
```

</details>

#### rejects revoked sessions even with a valid token

1. var key ring = RemoteSecuritySigningKeyRing new
2. var sessions = RemoteSecuritySessionStore new
3. sessions create session
4. sessions revoke session
   - Expected: ctx.is_authenticated() is false
   - Expected: ctx.session_id equals `session-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key_ring = RemoteSecuritySigningKeyRing.new("k1", "server-secret")
var sessions = RemoteSecuritySessionStore.new()
sessions.create_session("session-2", "user-2", ["admin.read"], 3000)
val token = sign_remote_security_token_with_key_ring(key_ring, "session-2", "user-2", 2500, ["admin.read"])
sessions.revoke_session("session-2")

val headers = RemoteSecurityContextHeaders(
    authorization: "Bearer {token}",
    traceparent: "",
    tenant_id: "",
    policy_version: "",
    request_class: ""
)

val ctx = validate_remote_security_context_with_key_ring(headers, "198.51.100.21", "session-2", key_ring, sessions, 2000)
expect(ctx.is_authenticated()).to_equal(false)
expect(ctx.session_id).to_equal("session-2")
```

</details>

#### allows refreshed sessions to outlive the original session expiry

1. var key ring = RemoteSecuritySigningKeyRing new
2. var sessions = RemoteSecuritySessionStore new
3. sessions create session
   - Expected: sessions.refresh_session("session-3", 4000) is true
   - Expected: ctx.is_authenticated() is true
   - Expected: ctx.user_id equals `user-3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key_ring = RemoteSecuritySigningKeyRing.new("k1", "server-secret")
var sessions = RemoteSecuritySessionStore.new()
sessions.create_session("session-3", "user-3", ["profile.write"], 2100)
expect(sessions.refresh_session("session-3", 4000)).to_equal(true)

val token = sign_remote_security_token_with_key_ring(key_ring, "session-3", "user-3", 3500, ["profile.write"])
val headers = RemoteSecurityContextHeaders(
    authorization: "Bearer {token}",
    traceparent: "",
    tenant_id: "",
    policy_version: "",
    request_class: ""
)

val ctx = validate_remote_security_context_with_key_ring(headers, "198.51.100.22", "session-3", key_ring, sessions, 3000)
expect(ctx.is_authenticated()).to_equal(true)
expect(ctx.user_id).to_equal("user-3")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/security/remote_security_lifecycle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- remote security lifecycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
