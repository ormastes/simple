# Mci Evidence Manifest V1 Specification

> Tests covering mission-critical evidence manifest v1.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mci Evidence Manifest V1 Specification

## Scenarios

### mission-critical evidence manifest v1

#### REQ-MCI-002 passes only a complete exact evidence set

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- REQ-MCI-002 passes only a complete exact evidence set
   - Expected: manifest.matrix.result equals `MCI_EVIDENCE_PASS`
   - Expected: manifest.matrix.blockers.len() equals `0`
   - Expected: manifest.matrix.rows.len() equals `2`
   - Expected: manifest.matrix.rows[0].check_id equals `compiler`
   - Expected: manifest.matrix.rows[1].check_id equals `render`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-MCI-002 passes only a complete exact evidence set")
val policy = mci_test_policy(["compiler", "render"])
val manifest = aggregate_mci_evidence_v1(policy,
    [mci_test_receipt(policy, "compiler"), mci_test_receipt(policy, "render")])
expect(manifest.matrix.result).to_equal(MCI_EVIDENCE_PASS)
expect(manifest.matrix.blockers.len()).to_equal(0)
expect(manifest.matrix.rows.len()).to_equal(2)
expect(manifest.matrix.rows[0].check_id).to_equal("compiler")
expect(manifest.matrix.rows[1].check_id).to_equal("render")
```

</details>

#### REQ-MCI-002 blocks missing duplicate and unexpected receipts

- REQ-MCI-002 blocks missing duplicate and unexpected receipts
   - Expected: manifest.matrix.result equals `MCI_EVIDENCE_BLOCKED`
   - Expected: mci_has_blocker(manifest, MCI_BLOCK_DUPLICATE) is true
   - Expected: mci_has_blocker(manifest, MCI_BLOCK_MISSING) is true
   - Expected: mci_has_blocker(manifest, MCI_BLOCK_UNEXPECTED) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-MCI-002 blocks missing duplicate and unexpected receipts")
val policy = mci_test_policy(["compiler", "render"])
val manifest = aggregate_mci_evidence_v1(policy,
    [mci_test_receipt(policy, "compiler"), mci_test_receipt(policy, "compiler"),
     mci_test_receipt(policy, "unknown")])
expect(manifest.matrix.result).to_equal(MCI_EVIDENCE_BLOCKED)
expect(mci_has_blocker(manifest, MCI_BLOCK_DUPLICATE)).to_equal(true)
expect(mci_has_blocker(manifest, MCI_BLOCK_MISSING)).to_equal(true)
expect(mci_has_blocker(manifest, MCI_BLOCK_UNEXPECTED)).to_equal(true)
```

</details>

#### REQ-MCI-002 never indexes the missing-receipt sentinel

- REQ-MCI-002 never indexes the missing-receipt sentinel
   - Expected: manifest.matrix.rows[0].receipt_index equals `-1`
   - Expected: manifest.matrix.rows[0].admitted is false
   - Expected: mci_has_blocker(manifest, MCI_BLOCK_MISSING) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-MCI-002 never indexes the missing-receipt sentinel")
val policy = mci_test_policy(["missing"])
val manifest = aggregate_mci_evidence_v1(policy, [])
expect(manifest.matrix.rows[0].receipt_index).to_equal(-1)
expect(manifest.matrix.rows[0].admitted).to_equal(false)
expect(mci_has_blocker(manifest, MCI_BLOCK_MISSING)).to_equal(true)
```

</details>

#### REQ-MCI-010 makes every invalid correlation an explicit blocker

- REQ-MCI-010 makes every invalid correlation an explicit blocker
   - Expected: mci_has_blocker(manifest, MCI_BLOCK_STALE) is true
   - Expected: mci_has_blocker(manifest, MCI_BLOCK_SKIPPED) is true
   - Expected: mci_has_blocker(manifest, MCI_BLOCK_WRONG_RUN) is true
   - Expected: mci_has_blocker(manifest, MCI_BLOCK_WRONG_SOURCE) is true
   - Expected: mci_has_blocker(manifest, MCI_BLOCK_WRONG_CONFIG) is true
   - Expected: mci_has_blocker(manifest, MCI_BLOCK_INVALID_HASH) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-MCI-010 makes every invalid correlation an explicit blocker")
val policy = mci_test_policy(["compiler"])
var receipt = mci_test_receipt(policy, "compiler")
receipt.valid_until_utc_ns = 99i64
receipt.result = MCI_EVIDENCE_SKIPPED
receipt.run_id = "wrong-run"
receipt.source_hash = "wrong-source"
receipt.configuration_hash = "wrong-config"
val manifest = aggregate_mci_evidence_v1(policy, [receipt])
expect(mci_has_blocker(manifest, MCI_BLOCK_STALE)).to_equal(true)
expect(mci_has_blocker(manifest, MCI_BLOCK_SKIPPED)).to_equal(true)
expect(mci_has_blocker(manifest, MCI_BLOCK_WRONG_RUN)).to_equal(true)
expect(mci_has_blocker(manifest, MCI_BLOCK_WRONG_SOURCE)).to_equal(true)
expect(mci_has_blocker(manifest, MCI_BLOCK_WRONG_CONFIG)).to_equal(true)
expect(mci_has_blocker(manifest, MCI_BLOCK_INVALID_HASH)).to_equal(true)
```

</details>

#### REQ-MCI-002 retains stable required order independent of receipt order

- REQ-MCI-002 retains stable required order independent of receipt order
   - Expected: manifest.matrix.result equals `MCI_EVIDENCE_PASS`
   - Expected: manifest.matrix.rows[0].check_id equals `compiler`
   - Expected: manifest.matrix.rows[1].check_id equals `os`
   - Expected: manifest.matrix.rows[2].check_id equals `render`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-MCI-002 retains stable required order independent of receipt order")
val policy = mci_test_policy(["compiler", "os", "render"])
val manifest = aggregate_mci_evidence_v1(policy,
    [mci_test_receipt(policy, "render"), mci_test_receipt(policy, "compiler"),
     mci_test_receipt(policy, "os")])
expect(manifest.matrix.result).to_equal(MCI_EVIDENCE_PASS)
expect(manifest.matrix.rows[0].check_id).to_equal("compiler")
expect(manifest.matrix.rows[1].check_id).to_equal("os")
expect(manifest.matrix.rows[2].check_id).to_equal("render")
```

</details>

#### REQ-MCI-010 blocks failed receipts and invalid empty policy

- REQ-MCI-010 blocks failed receipts and invalid empty policy
   - Expected: mci_has_blocker(failed_manifest, MCI_BLOCK_RECEIPT_FAILED) is true
   - Expected: invalid_manifest.matrix.result equals `MCI_EVIDENCE_BLOCKED`
   - Expected: mci_has_blocker(invalid_manifest, MCI_BLOCK_INVALID_HASH) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-MCI-010 blocks failed receipts and invalid empty policy")
val policy = mci_test_policy(["compiler"])
var failed = mci_test_receipt(policy, "compiler")
failed.result = MCI_EVIDENCE_FAIL
val failed_manifest = aggregate_mci_evidence_v1(policy, [failed])
expect(mci_has_blocker(failed_manifest, MCI_BLOCK_RECEIPT_FAILED)).to_equal(true)
val invalid_manifest = aggregate_mci_evidence_v1(mci_test_policy([]), [])
expect(invalid_manifest.matrix.result).to_equal(MCI_EVIDENCE_BLOCKED)
expect(mci_has_blocker(invalid_manifest, MCI_BLOCK_INVALID_HASH)).to_equal(true)
```

</details>

#### REQ-MCI-010 rejects receipt mutation and required-order replay

- REQ-MCI-010 rejects receipt mutation and required-order replay
   - Expected: mci_has_blocker(mutation_manifest, MCI_BLOCK_INVALID_HASH) is true
   - Expected: mci_has_blocker(replay_manifest, MCI_BLOCK_INVALID_HASH) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-MCI-010 rejects receipt mutation and required-order replay")
val policy = mci_test_policy(["compiler", "render"])
var mutated = mci_test_receipt(policy, "compiler")
mutated.valid_until_utc_ns = 201i64
val mutation_manifest = aggregate_mci_evidence_v1(policy,
    [mutated, mci_test_receipt(policy, "render")])
expect(mci_has_blocker(mutation_manifest, MCI_BLOCK_INVALID_HASH)).to_equal(true)

val reversed = mci_test_policy(["render", "compiler"])
val replay_manifest = aggregate_mci_evidence_v1(reversed,
    [mci_test_receipt(policy, "compiler"), mci_test_receipt(policy, "render")])
expect(mci_has_blocker(replay_manifest, MCI_BLOCK_INVALID_HASH)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/mission_critical/mci_evidence_manifest_v1_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering mission-critical evidence manifest v1.
- mission-critical evidence manifest v1

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `48888133044345fb16e2320c5e2a207bae926d2faf484017d09b173d89cb62cd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `48888133044345fb16e2320c5e2a207bae926d2faf484017d09b173d89cb62cd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `48888133044345fb16e2320c5e2a207bae926d2faf484017d09b173d89cb62cd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/mission_critical/mci_evidence_manifest_v1_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/mission_critical/mci_evidence_manifest_v1_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/mission_critical/mci_evidence_manifest_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/mission_critical/mci_evidence_manifest_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/mission_critical/mci_evidence_manifest_v1_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/mission_critical/mci_evidence_manifest_v1_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-MCI-002 passes only a complete exact evidence set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/mission_critical/mci_evidence_manifest_v1_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-MCI-002 blocks missing duplicate and unexpected receipts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/mission_critical/mci_evidence_manifest_v1_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-MCI-002 never indexes the missing-receipt sentinel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
