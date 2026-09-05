# Load Receipt Discrimination Specification

> Tests covering positive control — conforming load is GREEN, deviation is detectable, no constant receipts — different plans differ.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Load Receipt Discrimination Specification

## Scenarios

### positive control — conforming load is GREEN

#### receipt matching its plan passes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- receipt matching its plan passes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("receipt matching its plan passes")
val p = plan_with(3, 4096)
assert_true(load_receipt_check_against_plan(p, receipt_for(p, 3, 4096)).ok)
```

</details>

### deviation is detectable

#### plan says 3 segments, receipt says 5 — mismatch names segment_count

- plan says 3 segments, receipt says 5 — mismatch names segment_count


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("plan says 3 segments, receipt says 5 — mismatch names segment_count")
val p = plan_with(3, 4096)
val chk = load_receipt_check_against_plan(p, receipt_for(p, 5, 4096))
assert_false(chk.ok)
assert_true(chk.mismatch.contains("segment_count"))
assert_true(chk.mismatch.contains("3"))
assert_true(chk.mismatch.contains("5"))
```

</details>

#### bytes_mapped deviation is caught

- bytes_mapped deviation is caught


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bytes_mapped deviation is caught")
val p = plan_with(3, 4096)
val chk = load_receipt_check_against_plan(p, receipt_for(p, 3, 8192))
assert_false(chk.ok)
assert_true(chk.mismatch.contains("bytes_mapped"))
```

</details>

#### a receipt for a DIFFERENT plan is rejected via plan_hash

- a receipt for a DIFFERENT plan is rejected via plan_hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a receipt for a DIFFERENT plan is rejected via plan_hash")
val a = plan_with(3, 4096)
val b = plan_with(4, 4096)
val chk = load_receipt_check_against_plan(a, receipt_for(b, 4, 4096))
assert_false(chk.ok)
assert_true(chk.mismatch.contains("plan_hash"))
```

</details>

#### a plan altered after sealing is rejected

- a plan altered after sealing is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a plan altered after sealing is rejected")
var p = plan_with(3, 4096)
val r = receipt_for(p, 3, 4096)
p.planned_segment_count = 3
p.import_count = 99
val chk = load_receipt_check_against_plan(p, r)
assert_false(chk.ok)
```

</details>

#### a failed load result is never GREEN

- a failed load result is never GREEN


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a failed load result is never GREEN")
val p = plan_with(3, 4096)
val r = load_receipt_record(p, "sha256:feed", "posix_mmap", "dynamic",
                            4096, 4096, 3, 4, 2, -1, 1,
                            "miss", 1, "error", "mmap failed")
val chk = load_receipt_check_against_plan(p, r)
assert_false(chk.ok)
assert_true(chk.mismatch.contains("mmap failed"))
```

</details>

### no constant receipts — different plans differ

#### two different plans have different plan hashes

- two different plans have different plan hashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two different plans have different plan hashes")
val a = plan_with(3, 4096)
val b = plan_with(4, 4096)
assert_true(a.plan_hash != b.plan_hash)
```

</details>

#### receipts of two different plans carry different plan hashes

- receipts of two different plans carry different plan hashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("receipts of two different plans carry different plan hashes")
val a = plan_with(3, 4096)
val b = plan_with(3, 8192)
assert_true(receipt_for(a, 3, 4096).plan_hash != receipt_for(b, 3, 8192).plan_hash)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/startup/load_receipt_discrimination_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering positive control — conforming load is GREEN, deviation is detectable, no constant receipts — different plans differ.
- positive control — conforming load is GREEN
- deviation is detectable
- no constant receipts — different plans differ

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `6fbf29ad3eeac62816bbcd93f1b45fc7088bc3407f79951a06ebcb5b4f980798`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6fbf29ad3eeac62816bbcd93f1b45fc7088bc3407f79951a06ebcb5b4f980798`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6fbf29ad3eeac62816bbcd93f1b45fc7088bc3407f79951a06ebcb5b4f980798`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/startup/load_receipt_discrimination_spec.spl
mirror: doc/06_spec/01_unit/app/startup/load_receipt_discrimination_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/startup/load_receipt_discrimination_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/startup/load_receipt_discrimination_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/startup/load_receipt_discrimination_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'receipt matching its plan passes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/load_receipt_discrimination_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'plan says 3 segments, receipt says 5 — mismatch names segment_count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/load_receipt_discrimination_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bytes_mapped deviation is caught' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
