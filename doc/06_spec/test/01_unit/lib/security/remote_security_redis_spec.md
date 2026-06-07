# Remote Security Redis Specification

> <details>

<!-- sdn-diagram:id=remote_security_redis_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=remote_security_redis_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

remote_security_redis_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=remote_security_redis_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Remote Security Redis Specification

## Scenarios

### remote security Redis session adapter

#### serializes sessions with capabilities and revocation state

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = RemoteSecuritySession(
    session_id: "redis-session",
    user_id: "user-7",
    capabilities: ["profile.read", "billing.write"],
    expires_at_ms: 9000,
    revoked: false
)

val payload = remote_security_redis_encode_session(session)

expect(payload).to_equal("session|redis-session|user-7|9000|false|profile.read,billing.write")
```

</details>

#### decodes Redis session payloads

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = "session|redis-session|user-7|9000|false|profile.read,billing.write"
val decoded = remote_security_redis_decode_session(payload)

expect(decoded.?).to_equal(true)
```

</details>

#### preserves decoded user identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = "session|redis-session|user-7|9000|false|profile.read,billing.write"
val decoded = remote_security_redis_decode_session(payload)
expect(decoded.unwrap().user_id).to_equal("user-7")
```

</details>

#### preserves decoded capability lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = "session|redis-session|user-7|9000|false|profile.read,billing.write"
val decoded = remote_security_redis_decode_session(payload)
expect(decoded.unwrap().capabilities[1]).to_equal("billing.write")
```

</details>

#### uses bounded tombstone ttl for revoked sessions

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = RemoteSecuritySession(
    session_id: "revoked-redis-session",
    user_id: "user-8",
    capabilities: ["audit.read"],
    expires_at_ms: 9000,
    revoked: true
)

expect(remote_security_redis_session_ttl_seconds(session, 1000, 120)).to_equal(120)
expect(remote_security_redis_session_ttl_seconds(session, 1000, 0)).to_equal(1)
```

</details>

#### ceil-rounds active session expiry to Redis seconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = RemoteSecuritySession(
    session_id: "active-redis-session",
    user_id: "user-9",
    capabilities: ["audit.read"],
    expires_at_ms: 2501,
    revoked: false
)

expect(remote_security_redis_session_ttl_seconds(session, 1000, 120)).to_equal(2)
expect(remote_security_redis_session_ttl_seconds(session, 3000, 120)).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/security/remote_security_redis_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- remote security Redis session adapter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
