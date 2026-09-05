# Artifact Snapshot Specification

> Tests covering SimpleOS evidence byte-snapshot admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Artifact Snapshot Specification

## Scenarios

### SimpleOS evidence byte-snapshot admission

#### strictly decodes one canonical 64-byte signature

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-001
```

</details>

#### keeps independent owner and executable-evidence gates fail closed

- keeps independent owner and executable-evidence gates fail closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps independent owner and executable-evidence gates fail closed")
expect(simpleos_evidence_all_admission_gates_admitted()).to_be(false)
expect(simpleos_evidence_admission_gate_reason()).to_equal(
    "trust-root-owner-unavailable")
```

</details>

#### rehashes every signed payload class from exact bytes

- rehashes every signed payload class from exact bytes
   - Expected: checked.reason equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rehashes every signed payload class from exact bytes")
val checked = simpleos_evidence_artifact_snapshot_check(
    snapshot_candidate("snapshot-1"), snapshot_material())
expect(checked.ok).to_be(true)
expect(checked.reason).to_equal("")
```

</details>

#### rejects a changed config and a missing artifact snapshot

- rejects a changed config and a missing artifact snapshot
   - Expected: config_check.reason equals `config-rehash`
   - Expected: artifact_check.reason equals `artifact-snapshot-count`
   - Expected: fixture_check.reason equals `performance-fixture-binding`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a changed config and a missing artifact snapshot")
var changed = snapshot_material()
changed.config_bytes = [99u8]
val config_check = simpleos_evidence_artifact_snapshot_check(
    snapshot_candidate("snapshot-2"), changed)
expect(config_check.ok).to_be(false)
expect(config_check.reason).to_equal("config-rehash")

var missing = snapshot_material()
missing.artifact_bytes = []
val artifact_check = simpleos_evidence_artifact_snapshot_check(
    snapshot_candidate("snapshot-3"), missing)
expect(artifact_check.ok).to_be(false)
expect(artifact_check.reason).to_equal("artifact-snapshot-count")

var performance = snapshot_candidate("snapshot-performance")
var performance_receipt = performance.receipt
performance_receipt.performance_workload = "warm_server_startup"
performance.receipt = performance_receipt
val fixture_check = simpleos_evidence_artifact_snapshot_check(
    performance, snapshot_material())
expect(fixture_check.ok).to_be(false)
expect(fixture_check.reason).to_equal("performance-fixture-binding")
```

</details>

#### prepares an exact ledger value but grants no mutation authority

- prepares an exact ledger value but grants no mutation authority
   - Expected: original.revision equals `0`
   - Expected: original.rows.len() equals `0`
   - Expected: prepared.ledger.revision equals `1`
   - Expected: prepared.ledger.rows.len() equals `1`
   - Expected: prepared.ledger.consumed_nonces equals `["snapshot-ledger"]`
   - Expected: replay.reason equals `replayed-nonce`
   - Expected: replay.ledger.revision equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("prepares an exact ledger value but grants no mutation authority")
val original = simpleos_capability_ledger_v1()
val candidate = snapshot_candidate("snapshot-ledger")
val prepared = simpleos_evidence_prepare_ledger_transition(
    original, candidate)
expect(prepared.ok).to_be(true)
expect(original.revision).to_equal(0)
expect(original.rows.len()).to_equal(0)
expect(prepared.ledger.revision).to_equal(1)
expect(prepared.ledger.rows.len()).to_equal(1)
expect(prepared.ledger.consumed_nonces).to_equal(["snapshot-ledger"])

val replay = simpleos_evidence_prepare_ledger_transition(
    prepared.ledger, candidate)
expect(replay.ok).to_be(false)
expect(replay.reason).to_equal("replayed-nonce")
expect(replay.ledger.revision).to_equal(1)
```

</details>

#### quarantines an indeterminate unlock without undoing mutation

- quarantines an indeterminate unlock without undoing mutation
   - Expected: indeterminate.reason equals `serialization-indeterminate`
   - Expected: clean.reason equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("quarantines an indeterminate unlock without undoing mutation")
val indeterminate = simpleos_evidence_owner_unlock_outcome(
    true, false, false)
expect(indeterminate.authoritative).to_be(false)
expect(indeterminate.quarantined).to_be(true)
expect(indeterminate.mutation_retained).to_be(true)
expect(indeterminate.reason).to_equal("serialization-indeterminate")

val clean = simpleos_evidence_owner_unlock_outcome(false, true, false)
expect(clean.authoritative).to_be(true)
expect(clean.quarantined).to_be(false)
expect(clean.mutation_retained).to_be(false)
expect(clean.reason).to_equal("")
```

</details>

#### reaches the explicit crypto blocker only after an exact rehash

- reaches the explicit crypto blocker only after an exact rehash
   - Expected: root_rejected.reason equals `signer-untrusted`
   - Expected: verified.reason equals `trust-root-owner-unavailable`
   - Expected: verified.handle.handle_id equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reaches the explicit crypto blocker only after an exact rehash")
val started = simpleos_evidence_verifier_start([
    SimpleOsTrustedEvidenceSignerV1(
        key_id: "root-1", public_key: [7u8; 32])])
expect(started.ok).to_be(true)
val issued = simpleos_evidence_issue_challenge(
    "snapshot-live", 90, 100)
expect(issued.ok).to_be(true)
var untrusted = snapshot_candidate("snapshot-live")
var untrusted_receipt = untrusted.receipt
untrusted_receipt.signer_key_id = "other-root"
untrusted.receipt = untrusted_receipt
val root_rejected = simpleos_evidence_verify_candidate_with_snapshot(
    untrusted,
    issued.challenge,
    "snapshot-consumer",
    snapshot_material(),
    130)
expect(root_rejected.ok).to_be(false)
expect(root_rejected.reason).to_equal("signer-untrusted")
val verified = simpleos_evidence_verify_candidate_with_snapshot(
    snapshot_candidate("snapshot-live"),
    issued.challenge,
    "snapshot-consumer",
    snapshot_material(),
    130)
expect(verified.ok).to_be(false)
expect(verified.reason).to_equal("trust-root-owner-unavailable")
expect(verified.handle.handle_id).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/evidence/artifact_snapshot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS evidence byte-snapshot admission.
- SimpleOS evidence byte-snapshot admission

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
- `REQ-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4a8bc87f95c86249388fc78bf482db0b20205b6d095e920cd5140627df3c8f0c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4a8bc87f95c86249388fc78bf482db0b20205b6d095e920cd5140627df3c8f0c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4a8bc87f95c86249388fc78bf482db0b20205b6d095e920cd5140627df3c8f0c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/01_unit/os/services/evidence/artifact_snapshot_spec.spl
mirror: doc/06_spec/01_unit/os/services/evidence/artifact_snapshot_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/evidence/artifact_snapshot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/evidence/artifact_snapshot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/evidence/artifact_snapshot_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/services/evidence/artifact_snapshot_spec.spl:132:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'strictly decodes one canonical 64-byte signature' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/services/evidence/artifact_snapshot_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps independent owner and executable-evidence gates fail closed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/evidence/artifact_snapshot_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rehashes every signed payload class from exact bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/evidence/artifact_snapshot_spec.spl:161:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a changed config and a missing artifact snapshot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
