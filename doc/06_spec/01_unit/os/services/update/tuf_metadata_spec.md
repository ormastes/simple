# TUF Metadata Trust Model Specification (Phase 5 — updates/recovery)

> Models the four TUF roles (root, targets, snapshot, timestamp) and the trust structure that keeps the update system secure under repository or single-key compromise: signing thresholds, metadata freshness (freeze defense), version rollback defense, and snapshot consistency. Signatures are modeled as an already-verified key-id list — no real crypto, network, or install here.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TUF Metadata Trust Model Specification (Phase 5 — updates/recovery)

Models the four TUF roles (root, targets, snapshot, timestamp) and the trust structure that keeps the update system secure under repository or single-key compromise: signing thresholds, metadata freshness (freeze defense), version rollback defense, and snapshot consistency. Signatures are modeled as an already-verified key-id list — no real crypto, network, or install here.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Update security |
| Status | Model |
| Source | `test/01_unit/os/services/update/tuf_metadata_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Models the four TUF roles (root, targets, snapshot, timestamp) and the trust
structure that keeps the update system secure under repository or single-key
compromise: signing thresholds, metadata freshness (freeze defense), version
rollback defense, and snapshot consistency. Signatures are modeled as an
already-verified key-id list — no real crypto, network, or install here.

Absolute oracles: a well-formed update is ACCEPTED; each of five attacks is
REJECTED with its own distinct reason code.

## Scenarios

### TUF verifier primitives

#### rollback_guard accepts a higher incoming version

- rollback_guard accepts a higher incoming version


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rollback_guard accepts a higher incoming version")
"""incoming >= current is allowed."""
assert_true(rollback_guard(10, 11))
```

</details>

#### rollback_guard rejects a lower incoming version

- rollback_guard rejects a lower incoming version


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rollback_guard rejects a lower incoming version")
"""incoming < current is the rollback attack — denied."""
assert_false(rollback_guard(10, 9))
```

</details>

#### check_freshness accepts metadata before expiry

- check_freshness accepts metadata before expiry


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("check_freshness accepts metadata before expiry")
"""now <= expires_at stays fresh."""
val meta = mk_timestamp()
assert_true(check_freshness(meta, 1000))
```

</details>

#### check_freshness rejects expired metadata

- check_freshness rejects expired metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("check_freshness rejects expired metadata")
"""now past expires_at is a freeze/expiry failure."""
val meta = mk_timestamp()
assert_false(check_freshness(meta, 3000))
```

</details>

#### verify_threshold accepts when enough distinct valid signers signed

- verify_threshold accepts when enough distinct valid signers signed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify_threshold accepts when enough distinct valid signers signed")
"""root has 2 valid signatures and threshold 2."""
assert_true(verify_threshold(mk_root()))
```

</details>

#### verify_threshold rejects when signers fall below threshold

- verify_threshold rejects when signers fall below threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify_threshold rejects when signers fall below threshold")
"""A threshold-2 role with a single valid signer is denied."""
val weak = RoleMetadata(
    role: "targets", version: 11, expires_at: 2000, threshold: 2,
    signer_key_ids: ["tgt_k1", "tgt_k2"],
    signatures_present: ["tgt_k1"],
    delegated_key_ids: [], recorded_targets_version: 0)
assert_false(verify_threshold(weak))
```

</details>

#### verify_snapshot_consistency accepts matching targets versions

- verify_snapshot_consistency accepts matching targets versions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify_snapshot_consistency accepts matching targets versions")
"""snapshot vouches for exactly the presented targets version."""
assert_true(verify_snapshot_consistency(11, 11))
```

</details>

#### verify_snapshot_consistency rejects a version mismatch

- verify_snapshot_consistency rejects a version mismatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verify_snapshot_consistency rejects a version mismatch")
"""Mix-and-match of snapshot and targets is denied."""
assert_false(verify_snapshot_consistency(10, 11))
```

</details>

### TUF full verification — well-formed update
_A threshold-signed, fresh, forward-versioned, consistent update passes._

#### accepts a well-formed update

- accepts a well-formed update
   - Expected: outcome.accepted is true
   - Expected: outcome.reason_code equals `TUF_ACCEPTED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a well-formed update")
"""All four roles verify; outcome is accepted with reason code 0."""
val root = mk_root()
val ts = mk_timestamp()
val snap = mk_snapshot(11)
val tgt = mk_targets(11)
val outcome = verify_update(root, ts, snap, tgt, mk_current(), 1000)
expect(outcome.accepted).to_equal(true)
expect(outcome.reason_code).to_equal(TUF_ACCEPTED)
```

</details>

### TUF full verification — attacks rejected
_Every compromise scenario fails closed with a distinct reason code._

#### rejects below-threshold signatures

- rejects below-threshold signatures
   - Expected: outcome.accepted is false
   - Expected: outcome.reason_code equals `TUF_BAD_THRESHOLD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects below-threshold signatures")
"""A targets role signed under threshold yields TUF_BAD_THRESHOLD."""
val root = mk_root()
val ts = mk_timestamp()
val snap = mk_snapshot(11)
val tgt = RoleMetadata(
    role: "targets", version: 11, expires_at: 2000, threshold: 2,
    signer_key_ids: ["tgt_k1", "tgt_k2"],
    signatures_present: ["tgt_k1"],
    delegated_key_ids: [], recorded_targets_version: 0)
val outcome = verify_update(root, ts, snap, tgt, mk_current(), 1000)
expect(outcome.accepted).to_equal(false)
expect(outcome.reason_code).to_equal(TUF_BAD_THRESHOLD)
```

</details>

#### rejects an expired timestamp (freeze defense)

- rejects an expired timestamp (freeze defense)
   - Expected: outcome.accepted is false
   - Expected: outcome.reason_code equals `TUF_EXPIRED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an expired timestamp (freeze defense)")
"""now past every role's expiry yields TUF_EXPIRED."""
val root = mk_root()
val ts = mk_timestamp()
val snap = mk_snapshot(11)
val tgt = mk_targets(11)
val outcome = verify_update(root, ts, snap, tgt, mk_current(), 3000)
expect(outcome.accepted).to_equal(false)
expect(outcome.reason_code).to_equal(TUF_EXPIRED)
```

</details>

#### rejects a rollback to a lower targets version

- rejects a rollback to a lower targets version
   - Expected: outcome.accepted is false
   - Expected: outcome.reason_code equals `TUF_ROLLBACK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a rollback to a lower targets version")
"""A targets version below the current one yields TUF_ROLLBACK."""
val root = mk_root()
val ts = mk_timestamp()
val snap = mk_snapshot(9)
val tgt = mk_targets(9)
val outcome = verify_update(root, ts, snap, tgt, mk_current(), 1000)
expect(outcome.accepted).to_equal(false)
expect(outcome.reason_code).to_equal(TUF_ROLLBACK)
```

</details>

#### rejects a snapshot / targets version mismatch

- rejects a snapshot / targets version mismatch
   - Expected: outcome.accepted is false
   - Expected: outcome.reason_code equals `TUF_SNAPSHOT_MISMATCH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a snapshot / targets version mismatch")
"""Snapshot pinning a different targets version yields TUF_SNAPSHOT_MISMATCH."""
val root = mk_root()
val ts = mk_timestamp()
val snap = mk_snapshot(10)
val tgt = mk_targets(11)
val outcome = verify_update(root, ts, snap, tgt, mk_current(), 1000)
expect(outcome.accepted).to_equal(false)
expect(outcome.reason_code).to_equal(TUF_SNAPSHOT_MISMATCH)
```

</details>

#### rejects a signer key not in root's trusted set

- rejects a signer key not in root's trusted set
   - Expected: outcome.accepted is false
   - Expected: outcome.reason_code equals `TUF_UNTRUSTED_KEY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a signer key not in root's trusted set")
"""An untrusted signing key yields TUF_UNTRUSTED_KEY."""
val root = mk_root()
val ts = mk_timestamp()
val snap = mk_snapshot(11)
val tgt = RoleMetadata(
    role: "targets", version: 11, expires_at: 2000, threshold: 1,
    signer_key_ids: ["attacker_k"],
    signatures_present: ["attacker_k"],
    delegated_key_ids: [], recorded_targets_version: 0)
val outcome = verify_update(root, ts, snap, tgt, mk_current(), 1000)
expect(outcome.accepted).to_equal(false)
expect(outcome.reason_code).to_equal(TUF_UNTRUSTED_KEY)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `558ce1b0c5a6783c303912ffdb6b95ab3f0caefb92fe1d5924d678218c12db07`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `558ce1b0c5a6783c303912ffdb6b95ab3f0caefb92fe1d5924d678218c12db07`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `558ce1b0c5a6783c303912ffdb6b95ab3f0caefb92fe1d5924d678218c12db07`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/01_unit/os/services/update/tuf_metadata_spec.spl
mirror: doc/06_spec/01_unit/os/services/update/tuf_metadata_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=80
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/update/tuf_metadata_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/update/tuf_metadata_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rollback_guard accepts a higher incoming version' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/update/tuf_metadata_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rollback_guard rejects a lower incoming version' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/update/tuf_metadata_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'check_freshness accepts metadata before expiry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
