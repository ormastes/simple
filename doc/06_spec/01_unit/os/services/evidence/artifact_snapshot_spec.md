# artifact_snapshot_spec

> Verifies the artifact snapshot behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# artifact_snapshot_spec

Verifies the artifact snapshot behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/evidence/artifact_snapshot_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the artifact snapshot behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### SimpleOS evidence byte-snapshot admission

#### strictly decodes one canonical 64-byte signature

- Verify: strictly decodes one canonical 64-byte signature
   - Expected: simpleos_evidence_signature_hex_decode(zero_signature).len() equals `64)  # oracle: pinned constant asserted by this scenario`
   - Expected: simpleos_evidence_signature_hex_decode("00").len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: simpleos_evidence_signature_hex_decode(invalid).len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001
step("Verify: strictly decodes one canonical 64-byte signature")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val zero_signature =
    "0000000000000000000000000000000000000000000000000000000000000000" +
    "0000000000000000000000000000000000000000000000000000000000000000"
expect(simpleos_evidence_signature_hex_decode(zero_signature).len()).to_equal(64)  # oracle: pinned constant asserted by this scenario
expect(simpleos_evidence_signature_hex_decode("00").len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
var invalid = zero_signature
invalid = "z" + invalid.substring(1, invalid.len())
expect(simpleos_evidence_signature_hex_decode(invalid).len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### keeps independent owner and executable-evidence gates fail closed

- Verify: keeps independent owner and executable-evidence gates fail closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001
step("Verify: keeps independent owner and executable-evidence gates fail closed")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(simpleos_evidence_all_admission_gates_admitted()).to_be(false)
expect(simpleos_evidence_admission_gate_reason()).to_equal(
    "trust-root-owner-unavailable")
```

</details>

#### rehashes every signed payload class from exact bytes

- Verify: rehashes every signed payload class from exact bytes
   - Expected: checked.reason equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001
step("Verify: rehashes every signed payload class from exact bytes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val checked = simpleos_evidence_artifact_snapshot_check(
    snapshot_candidate("snapshot-1"), snapshot_material())
expect(checked.ok).to_be(true)
expect(checked.reason).to_equal("")
```

</details>

#### rejects a changed config and a missing artifact snapshot

- Verify: rejects a changed config and a missing artifact snapshot
   - Expected: config_check.reason equals `config-rehash`
   - Expected: artifact_check.reason equals `artifact-snapshot-count`
   - Expected: fixture_check.reason equals `performance-fixture-binding`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001
step("Verify: rejects a changed config and a missing artifact snapshot")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: prepares an exact ledger value but grants no mutation authority
   - Expected: original.revision equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: original.rows.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: prepared.ledger.revision equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: prepared.ledger.rows.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: prepared.ledger.consumed_nonces equals `["snapshot-ledger"]`
   - Expected: replay.reason equals `replayed-nonce`
   - Expected: replay.ledger.revision equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001
step("Verify: prepares an exact ledger value but grants no mutation authority")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val original = simpleos_capability_ledger_v1()
val candidate = snapshot_candidate("snapshot-ledger")
val prepared = simpleos_evidence_prepare_ledger_transition(
    original, candidate)
expect(prepared.ok).to_be(true)
expect(original.revision).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(original.rows.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(prepared.ledger.revision).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(prepared.ledger.rows.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(prepared.ledger.consumed_nonces).to_equal(["snapshot-ledger"])

val replay = simpleos_evidence_prepare_ledger_transition(
    prepared.ledger, candidate)
expect(replay.ok).to_be(false)
expect(replay.reason).to_equal("replayed-nonce")
expect(replay.ledger.revision).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### quarantines an indeterminate unlock without undoing mutation

- Verify: quarantines an indeterminate unlock without undoing mutation
   - Expected: indeterminate.reason equals `serialization-indeterminate`
   - Expected: clean.reason equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001
step("Verify: quarantines an indeterminate unlock without undoing mutation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: reaches the explicit crypto blocker only after an exact rehash
   - Expected: root_rejected.reason equals `signer-untrusted`
   - Expected: verified.reason equals `trust-root-owner-unavailable`
   - Expected: verified.handle.handle_id equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001
step("Verify: reaches the explicit crypto blocker only after an exact rehash")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `db17c54fdffab3dc8ec8a2e75b44f12d122d6cc6329e7b6fc8a97915154a6e23`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db17c54fdffab3dc8ec8a2e75b44f12d122d6cc6329e7b6fc8a97915154a6e23`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db17c54fdffab3dc8ec8a2e75b44f12d122d6cc6329e7b6fc8a97915154a6e23`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/services/evidence/artifact_snapshot_spec.spl
mirror: doc/06_spec/01_unit/os/services/evidence/artifact_snapshot_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/evidence/artifact_snapshot_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/services/evidence/artifact_snapshot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/evidence/artifact_snapshot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
