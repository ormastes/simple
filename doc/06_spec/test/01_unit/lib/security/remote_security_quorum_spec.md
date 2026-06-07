# Remote Security Quorum Specification

> 1. var replica a = RemoteSecuritySessionStoreAdapter replicated

<!-- sdn-diagram:id=remote_security_quorum_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=remote_security_quorum_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

remote_security_quorum_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=remote_security_quorum_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Remote Security Quorum Specification

## Scenarios

### remote security quorum session store

#### reports write quorum success

1. var replica a = RemoteSecuritySessionStoreAdapter replicated
2. var replica b = RemoteSecuritySessionStoreAdapter replicated
3. var replica c = RemoteSecuritySessionStoreAdapter replicated
4. var quorum = RemoteSecurityQuorumSessionStore new
   - Expected: quorum.create_session("write-only-session", "user-10", ["profile.read"], 9000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var replica_a = RemoteSecuritySessionStoreAdapter.replicated("redis", "security:a")
var replica_b = RemoteSecuritySessionStoreAdapter.replicated("redis", "security:b")
var replica_c = RemoteSecuritySessionStoreAdapter.replicated("redis", "security:c")
var quorum = RemoteSecurityQuorumSessionStore.new([replica_a, replica_b, replica_c], 2, 2)

expect(quorum.create_session("write-only-session", "user-10", ["profile.read"], 9000)).to_equal(true)
```

</details>

#### clamps impossible quorum counts to the replica count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(remote_security_quorum_clamp(0, 3)).to_equal(1)
expect(remote_security_quorum_clamp(5, 3)).to_equal(3)
expect(remote_security_quorum_clamp(2, 3)).to_equal(2)
```

</details>

#### chooses the later active expiry when no revocation is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val older = quorum_session("merge-session", 4000, false, ["profile.read"])
val newer = quorum_session("merge-session", 9000, false, ["profile.read", "billing.write"])
val winner = remote_security_quorum_pick(Some(older), newer)
val loaded: RemoteSecuritySession = winner.unwrap()

expect(loaded.expires_at_ms).to_equal(9000)
expect(loaded.capabilities[1]).to_equal("billing.write")
```

</details>

#### lets revocation win over a later active session

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val active = quorum_session("revoked-session", 9000, false, ["admin.read"])
val revoked = quorum_session("revoked-session", 4000, true, ["admin.read"])
val winner = remote_security_quorum_pick(Some(active), revoked)
val loaded: RemoteSecuritySession = winner.unwrap()

expect(loaded.revoked).to_equal(true)
```

</details>

#### exports quorum topology without session payloads

1. var replica a = RemoteSecuritySessionStoreAdapter replicated
2. var replica b = RemoteSecuritySessionStoreAdapter replicated
3. var replica c = RemoteSecuritySessionStoreAdapter replicated
4. var quorum = RemoteSecurityQuorumSessionStore new


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var replica_a = RemoteSecuritySessionStoreAdapter.replicated("redis", "security:a")
var replica_b = RemoteSecuritySessionStoreAdapter.replicated("redis", "security:b")
var replica_c = RemoteSecuritySessionStoreAdapter.replicated("redis", "security:c")
var quorum = RemoteSecurityQuorumSessionStore.new([replica_a, replica_b, replica_c], 2, 2)

val sdn = quorum.export_sdn()

expect(sdn).to_contain("remote_security_quorum_session_store:")
expect(sdn).to_contain("read_quorum: 2")
expect(sdn).to_contain("write_quorum: 2")
expect(sdn).to_contain("replica|1|redis|security:b")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/security/remote_security_quorum_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- remote security quorum session store

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
