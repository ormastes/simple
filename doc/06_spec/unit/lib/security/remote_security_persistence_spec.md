# Remote Security Persistence Specification

> Tests covering remote security persistence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Remote Security Persistence Specification

## Scenarios

### remote security persistence

#### reloads key ring and sessions from SDN export

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reloads key ring and sessions from SDN export
   - Expected: ctx.is_authenticated() is true
   - Expected: ctx.has_capability("profile.write") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reloads key ring and sessions from SDN export")
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

- merges later expiry while propagating revocation
   - Expected: refreshed_ctx.is_authenticated() is true
   - Expected: refreshed_ctx.has_capability("admin.write") is true
   - Expected: revoked_ctx.is_authenticated() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("merges later expiry while propagating revocation")
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

- keeps rotated keys across reload and rejects retired keys
   - Expected: old_ctx.is_authenticated() is true
   - Expected: new_ctx.is_authenticated() is true
   - Expected: retired_ctx.is_authenticated() is false
   - Expected: active_ctx.is_authenticated() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps rotated keys across reload and rejects retired keys")
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

- validates through replicated session and opaque key rollout adapters
   - Expected: ctx.is_authenticated() is true
   - Expected: ctx.has_capability("billing.write") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates through replicated session and opaque key rollout adapters")
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

- rejects adapter validation after external key retirement or session revocation
   - Expected: retired_ctx.is_authenticated() is false
   - Expected: revoked_ctx.is_authenticated() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects adapter validation after external key retirement or session revocation")
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
| Source | `test/unit/lib/security/remote_security_persistence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering remote security persistence.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `88b8cdd7d967efcc3de1df2b6df0a392a673f5e51a3edd4b2ddd46d7e9ff6713`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `88b8cdd7d967efcc3de1df2b6df0a392a673f5e51a3edd4b2ddd46d7e9ff6713`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `88b8cdd7d967efcc3de1df2b6df0a392a673f5e51a3edd4b2ddd46d7e9ff6713`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/security/remote_security_persistence_spec.spl
mirror: doc/06_spec/unit/lib/security/remote_security_persistence_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/security/remote_security_persistence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/security/remote_security_persistence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/security/remote_security_persistence_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reloads key ring and sessions from SDN export' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/security/remote_security_persistence_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'merges later expiry while propagating revocation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/security/remote_security_persistence_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps rotated keys across reload and rejects retired keys' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
