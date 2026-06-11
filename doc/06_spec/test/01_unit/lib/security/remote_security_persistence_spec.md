# Remote Security Persistence Specification

> 1. var key ring = RemoteSecuritySigningKeyRing new

<!-- sdn-diagram:id=remote_security_persistence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=remote_security_persistence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

remote_security_persistence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=remote_security_persistence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Remote Security Persistence Specification

## Scenarios

### remote security persistence

#### reloads key ring and sessions from SDN export

1. var key ring = RemoteSecuritySigningKeyRing new
2. key ring rotate key
3. var sessions = RemoteSecuritySessionStore new
4. sessions create session
   - Expected: ctx.is_authenticated() is true
   - Expected: ctx.has_capability("profile.write") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key_ring = RemoteSecuritySigningKeyRing.new("k1", "old-secret")
key_ring.rotate_key("k2", "new-secret")
var sessions = RemoteSecuritySessionStore.new()
sessions.create_session("persisted-session", "user-1", ["profile.read", "profile.write"], 9000)

val key_sdn = key_ring.export_sdn()
val session_sdn = sessions.export_sdn()
val loaded_keys = RemoteSecuritySigningKeyRing.from_sdn(key_sdn)
val loaded_sessions = RemoteSecuritySessionStore.from_sdn(session_sdn)

val token = sign_remote_security_token_with_key_ring(loaded_keys, "persisted-session", "user-1", 8000, ["profile.read"])
val ctx = validate_remote_security_context_with_key_ring(bearer_headers(token), "198.51.100.30", "persisted-session", loaded_keys, loaded_sessions, 2000)

expect(key_sdn).to_contain("active: k2")
expect(session_sdn).to_contain("session|persisted-session|user-1|9000|false|profile.read,profile.write")
expect(ctx.is_authenticated()).to_equal(true)
expect(ctx.has_capability("profile.write")).to_equal(true)
```

</details>

#### merges later expiry while propagating revocation

1. var primary = RemoteSecuritySessionStore new
2. primary create session
3. var replica = RemoteSecuritySessionStore new
4. replica create session
5. primary merge from
6. var key ring = RemoteSecuritySigningKeyRing new
   - Expected: refreshed_ctx.is_authenticated() is true
   - Expected: refreshed_ctx.has_capability("admin.write") is true
7. replica revoke session
8. primary merge from
   - Expected: revoked_ctx.is_authenticated() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var primary = RemoteSecuritySessionStore.new()
primary.create_session("shared-session", "user-2", ["admin.read"], 4000)
var replica = RemoteSecuritySessionStore.new()
replica.create_session("shared-session", "user-2", ["admin.read", "admin.write"], 7000)

primary.merge_from(replica)

var key_ring = RemoteSecuritySigningKeyRing.new("k1", "server-secret")
val refreshed_token = sign_remote_security_token_with_key_ring(key_ring, "shared-session", "user-2", 6500, ["admin.read"])
val refreshed_ctx = validate_remote_security_context_with_key_ring(bearer_headers(refreshed_token), "198.51.100.31", "shared-session", key_ring, primary, 5000)
expect(refreshed_ctx.is_authenticated()).to_equal(true)
expect(refreshed_ctx.has_capability("admin.write")).to_equal(true)

replica.revoke_session("shared-session")
primary.merge_from(replica)

val revoked_ctx = validate_remote_security_context_with_key_ring(bearer_headers(refreshed_token), "198.51.100.31", "shared-session", key_ring, primary, 5000)
expect(revoked_ctx.is_authenticated()).to_equal(false)
```

</details>

#### keeps rotated keys across reload and rejects retired keys

1. var key ring = RemoteSecuritySigningKeyRing new
2. var sessions = RemoteSecuritySessionStore new
3. sessions create session
4. var peer keys = RemoteSecuritySigningKeyRing new
5. peer keys rotate key
6. key ring merge from
7. var loaded keys = RemoteSecuritySigningKeyRing from sdn
   - Expected: old_ctx.is_authenticated() is true
   - Expected: new_ctx.is_authenticated() is true
8. loaded keys retire key
   - Expected: retired_ctx.is_authenticated() is false
   - Expected: active_ctx.is_authenticated() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key_ring = RemoteSecuritySigningKeyRing.new("k1", "old-secret")
var sessions = RemoteSecuritySessionStore.new()
sessions.create_session("rotated-session", "user-3", ["profile.read"], 9000)
val old_token = sign_remote_security_token_with_key_ring(key_ring, "rotated-session", "user-3", 8000, ["profile.read"])

var peer_keys = RemoteSecuritySigningKeyRing.new("k1", "old-secret")
peer_keys.rotate_key("k2", "new-secret")
key_ring.merge_from(peer_keys)
val new_token = sign_remote_security_token_with_key_ring(key_ring, "rotated-session", "user-3", 8000, ["profile.read"])
var loaded_keys = RemoteSecuritySigningKeyRing.from_sdn(key_ring.export_sdn())

val old_ctx = validate_remote_security_context_with_key_ring(bearer_headers(old_token), "198.51.100.32", "rotated-session", loaded_keys, sessions, 2000)
val new_ctx = validate_remote_security_context_with_key_ring(bearer_headers(new_token), "198.51.100.32", "rotated-session", loaded_keys, sessions, 2000)
expect(old_ctx.is_authenticated()).to_equal(true)
expect(new_ctx.is_authenticated()).to_equal(true)

loaded_keys.retire_key("k1")
val retired_ctx = validate_remote_security_context_with_key_ring(bearer_headers(old_token), "198.51.100.32", "rotated-session", loaded_keys, sessions, 2000)
val active_ctx = validate_remote_security_context_with_key_ring(bearer_headers(new_token), "198.51.100.32", "rotated-session", loaded_keys, sessions, 2000)
expect(retired_ctx.is_authenticated()).to_equal(false)
expect(active_ctx.is_authenticated()).to_equal(true)
```

</details>

#### validates through replicated session and opaque key rollout adapters

1. var sessions = RemoteSecuritySessionStoreAdapter replicated
2. sessions create session
3. var key provider = RemoteSecurityKeyRolloutProvider with active key
4. key provider allow external signature
   - Expected: ctx.is_authenticated() is true
   - Expected: ctx.has_capability("billing.write") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sessions = RemoteSecuritySessionStoreAdapter.replicated("redis", "security:session")
sessions.create_session("adapter-session", "user-4", ["billing.read", "billing.write"], 9000)
var key_provider = RemoteSecurityKeyRolloutProvider.with_active_key("kms-key-1", "kms://security/kms-key-1")
val payload = remote_security_token_payload_v2("kms-key-1", "adapter-session", "user-4", 8000, ["billing.read"])
val signature = "external-signature-1"
key_provider.allow_external_signature("kms-key-1", payload, signature)
val token = remote_security_token_with_external_signature("kms-key-1", "adapter-session", "user-4", 8000, ["billing.read"], signature)

val ctx = validate_remote_security_context_with_adapters(bearer_headers(token), "198.51.100.33", "adapter-session", key_provider, sessions, 2000)

expect(sessions.export_sdn()).to_contain("backend: redis")
expect(key_provider.export_sdn()).to_contain("key_handle|kms-key-1|kms://security/kms-key-1")
expect(ctx.is_authenticated()).to_equal(true)
expect(ctx.has_capability("billing.write")).to_equal(true)
```

</details>

#### rejects adapter validation after external key retirement or session revocation

1. var sessions = RemoteSecuritySessionStoreAdapter replicated
2. sessions create session
3. var key provider = RemoteSecurityKeyRolloutProvider with active key
4. key provider allow external signature
5. key provider retire key
   - Expected: retired_ctx.is_authenticated() is false
6. key provider rotate key
7. key provider allow external signature
8. sessions revoke session
   - Expected: revoked_ctx.is_authenticated() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sessions = RemoteSecuritySessionStoreAdapter.replicated("redis", "security:session")
sessions.create_session("revoked-adapter-session", "user-5", ["audit.read"], 9000)
var key_provider = RemoteSecurityKeyRolloutProvider.with_active_key("hsm-key-1", "hsm://cluster/key-1")
val payload = remote_security_token_payload_v2("hsm-key-1", "revoked-adapter-session", "user-5", 8000, ["audit.read"])
key_provider.allow_external_signature("hsm-key-1", payload, "sig")
val token = remote_security_token_with_external_signature("hsm-key-1", "revoked-adapter-session", "user-5", 8000, ["audit.read"], "sig")

key_provider.retire_key("hsm-key-1")
val retired_ctx = validate_remote_security_context_with_adapters(bearer_headers(token), "198.51.100.34", "revoked-adapter-session", key_provider, sessions, 2000)
expect(retired_ctx.is_authenticated()).to_equal(false)

key_provider.rotate_key("hsm-key-1", "hsm://cluster/key-1")
key_provider.allow_external_signature("hsm-key-1", payload, "sig")
sessions.revoke_session("revoked-adapter-session")
val revoked_ctx = validate_remote_security_context_with_adapters(bearer_headers(token), "198.51.100.34", "revoked-adapter-session", key_provider, sessions, 2000)
expect(revoked_ctx.is_authenticated()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/security/remote_security_persistence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- remote security persistence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
