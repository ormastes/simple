# Snapshot Contract Specification

> Tests covering CAS-bound index operations and replay.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Snapshot Contract Specification

## Scenarios

### CAS-bound index operations and replay

#### requires paired replace/delete preconditions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires paired replace/delete preconditions
- Validate closed precondition choices
   - Expected: IndexOperationV1.replace("r1", "sha256:old", scoped_doc()).has_closed_preconditions() is true
   - Expected: IndexOperationV1.delete_absent("missing").has_closed_preconditions() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires paired replace/delete preconditions")
step("Validate closed precondition choices")
expect(IndexOperationV1.replace("r1", "sha256:old", scoped_doc()).has_closed_preconditions()).to_equal(true)
expect(IndexOperationV1.delete_absent("missing").has_closed_preconditions()).to_equal(true)
```

</details>

#### accepts byte-identical replay and rejects operation conflicts

- accepts byte-identical replay and rejects operation conflicts
- Validate replay operation and payload binding
   - Expected: replay.accepts("op", "sha256:p").is_ok() is true
   - Expected: replay.accepts("op", "sha256:other").is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts byte-identical replay and rejects operation conflicts")
step("Validate replay operation and payload binding")
val receipt = OperationReceiptV1(operation_id: "op", payload_hash: "sha256:p", scope_digest: "sha256:s", outcome: "applied", result_hash: "sha256:r", signature: "sig")
val replay = ReplayRecordV1(operation_id: "op", payload_hash: "sha256:p", result_bytes_hash: "sha256:r", receipt: receipt)
expect(replay.accepts("op", "sha256:p").is_ok()).to_equal(true)
expect(replay.accepts("op", "sha256:other").is_ok()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/search/snapshot_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CAS-bound index operations and replay.
- CAS-bound index operations and replay

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `9b33aef00e0a8db36e95648758c08530afcf01b2a8af1b82c721c56234b0ea73`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9b33aef00e0a8db36e95648758c08530afcf01b2a8af1b82c721c56234b0ea73`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9b33aef00e0a8db36e95648758c08530afcf01b2a8af1b82c721c56234b0ea73`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/common/search/snapshot_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/common/search/snapshot_contract_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/search/snapshot_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/search/snapshot_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/search/snapshot_contract_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires paired replace/delete preconditions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/search/snapshot_contract_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts byte-identical replay and rejects operation conflicts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
