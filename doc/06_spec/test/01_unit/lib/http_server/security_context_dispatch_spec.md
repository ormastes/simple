# Security Context Dispatch Specification

> <details>

<!-- sdn-diagram:id=security_context_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=security_context_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

security_context_dispatch_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=security_context_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Security Context Dispatch Specification

## Scenarios

### http security context dispatch

#### scopes remote SecurityContext around handler dispatch only

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = dispatch_handler_with_remote_security_context(observed_security_context_handler, test_location(), test_request())
expect(response.status).to_equal(200)
expect(response.body).to_equal("198.51.100.30|session-transport|false")
expect(current_security_context().is_authenticated()).to_equal(false)
```

</details>

#### authenticates handler dispatch only with a validated remote token

1.
2.
   - Expected: response.status equals `200`
   - Expected: response.body equals `198.51.100.30|session-transport|true`
   - Expected: current_security_context().is_authenticated() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = sign_remote_security_token("server-secret", "session-transport", "user-1", 2000, ["user.profile.write"])
val request = HttpRequestData(
    method: "GET",
    path: "/secure",
    query: "",
    version: "HTTP/1.1",
    headers: [
        ("Authorization", "Bearer {token}"),
        ("X-Simple-Session-Id", "session-transport")
    ],
    body: "",
    params: {},
    peer_addr: "198.51.100.30"
)
val response = dispatch_handler_with_validated_remote_security_context(observed_security_context_handler, test_location(), request, "server-secret", 1999)
expect(response.status).to_equal(200)
expect(response.body).to_equal("198.51.100.30|session-transport|true")
expect(current_security_context().is_authenticated()).to_equal(false)
```

</details>

#### keeps validated dispatch anonymous when token validation fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = test_request()
val response = dispatch_handler_with_validated_remote_security_context(observed_security_context_handler, test_location(), request, "server-secret", 1999)
expect(response.status).to_equal(200)
expect(response.body).to_equal("198.51.100.30|session-transport|false")
```

</details>

#### authenticates handler dispatch through external key and session adapters

1. var sessions = RemoteSecuritySessionStoreAdapter replicated
2. sessions create session
3. var key provider = RemoteSecurityKeyRolloutProvider with active key
4. key provider allow external signature
5.
6.
   - Expected: response.status equals `200`
   - Expected: response.body equals `198.51.100.30|session-transport|true`
   - Expected: current_security_context().is_authenticated() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sessions = RemoteSecuritySessionStoreAdapter.replicated("redis", "security:session")
sessions.create_session("session-transport", "user-1", ["user.profile.write"], 3000)
var key_provider = RemoteSecurityKeyRolloutProvider.with_active_key("kms-key-1", "kms://security/kms-key-1")
val payload = remote_security_token_payload_v2("kms-key-1", "session-transport", "user-1", 2500, ["user.profile.write"])
key_provider.allow_external_signature("kms-key-1", payload, "external-sig")
val token = remote_security_token_with_external_signature("kms-key-1", "session-transport", "user-1", 2500, ["user.profile.write"], "external-sig")
val request = HttpRequestData(
    method: "GET",
    path: "/secure",
    query: "",
    version: "HTTP/1.1",
    headers: [
        ("Authorization", "Bearer {token}"),
        ("X-Simple-Session-Id", "session-transport")
    ],
    body: "",
    params: {},
    peer_addr: "198.51.100.30"
)

val response = dispatch_handler_with_adapter_validated_remote_security_context(observed_security_context_handler, test_location(), request, key_provider, sessions, 1999)
expect(response.status).to_equal(200)
expect(response.body).to_equal("198.51.100.30|session-transport|true")
expect(current_security_context().is_authenticated()).to_equal(false)
```

</details>

#### authenticates handler dispatch through v2 key ring and session store

1. var key ring = RemoteSecuritySigningKeyRing new
2. key ring rotate key
3. var sessions = RemoteSecuritySessionStore new
4. sessions create session
5.
6.
   - Expected: response.status equals `200`
   - Expected: response.body equals `198.51.100.30|session-transport|true`
7. sessions revoke session
   - Expected: revoked_response.body equals `198.51.100.30|session-transport|false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key_ring = RemoteSecuritySigningKeyRing.new("k1", "old-secret")
key_ring.rotate_key("k2", "new-secret")
var sessions = RemoteSecuritySessionStore.new()
sessions.create_session("session-transport", "user-1", ["user.profile.write"], 3000)
val token = sign_remote_security_token_with_key_ring(key_ring, "session-transport", "user-1", 2500, ["user.profile.write"])
val request = HttpRequestData(
    method: "GET",
    path: "/secure",
    query: "",
    version: "HTTP/1.1",
    headers: [
        ("Authorization", "Bearer {token}"),
        ("X-Simple-Session-Id", "session-transport")
    ],
    body: "",
    params: {},
    peer_addr: "198.51.100.30"
)

val response = dispatch_handler_with_key_ring_validated_remote_security_context(observed_security_context_handler, test_location(), request, key_ring, sessions, 1999)
expect(response.status).to_equal(200)
expect(response.body).to_equal("198.51.100.30|session-transport|true")

sessions.revoke_session("session-transport")
val revoked_response = dispatch_handler_with_key_ring_validated_remote_security_context(observed_security_context_handler, test_location(), request, key_ring, sessions, 1999)
expect(revoked_response.body).to_equal("198.51.100.30|session-transport|false")
```

</details>

#### scopes remote context to an explicit HTTP task id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = dispatch_handler_with_task_security_context("task-http", observed_task_security_context_handler, test_location(), test_request())
expect(response.status).to_equal(200)
expect(response.body).to_equal("198.51.100.30|session-transport|false")
expect(current_task_security_context("task-http").is_authenticated()).to_equal(false)
expect(current_security_context().is_authenticated()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/http_server/security_context_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- http security context dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
