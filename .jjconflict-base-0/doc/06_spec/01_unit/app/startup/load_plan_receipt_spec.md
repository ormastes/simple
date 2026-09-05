# Load Plan Receipt Specification

> Tests covering load plan sealing, a conforming load produces a matching receipt.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Load Plan Receipt Specification

## Scenarios

### load plan sealing

#### seals a plan with a non-empty stable hash

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- seals a plan with a non-empty stable hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("seals a plan with a non-empty stable hash")
val p = sample_plan()
assert_true(p.plan_hash != "")
assert_eq(p.plan_hash, load_plan_hash(p))
```

</details>

#### renders SDN with header and plan_hash row

- renders SDN with header and plan_hash row


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders SDN with header and plan_hash row")
val sdn = load_plan_to_sdn(sample_plan())
assert_true(sdn.contains("load_plan:"))
assert_true(sdn.contains("  planned_segment_count: 3"))
assert_true(sdn.contains("  plan_hash: "))
```

</details>

### a conforming load produces a matching receipt

#### receipt recorded with the planned counts checks GREEN

- receipt recorded with the planned counts checks GREEN


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("receipt recorded with the planned counts checks GREEN")
val p = sample_plan()
val r = load_receipt_record(p, "sha256:feed", "posix_mmap", "dynamic",
                            8192, 8192, 3, 12, 5, -1, 2,
                            "hit", 4, "ok", "")
assert_eq(r.plan_hash, p.plan_hash)
val chk = load_receipt_check_against_plan(p, r)
assert_true(chk.ok)
assert_eq(chk.mismatch, "")
```

</details>

#### receipt renders as SDN with observed counts

- receipt renders as SDN with observed counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("receipt renders as SDN with observed counts")
val p = sample_plan()
val r = load_receipt_record(p, "sha256:feed", "posix_mmap", "dynamic",
                            8192, 8192, 3, 12, 5, -1, 2,
                            "hit", 4, "ok", "")
val sdn = load_receipt_to_sdn(r)
assert_true(sdn.contains("load_receipt:"))
assert_true(sdn.contains("  segment_count: 3"))
assert_true(sdn.contains("  plan_hash: " + p.plan_hash))
```

</details>

#### optional page_faults does not affect the verdict

- optional page_faults does not affect the verdict


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional page_faults does not affect the verdict")
val p = sample_plan()
val r = load_receipt_record(p, "sha256:feed", "posix_mmap", "dynamic",
                            8192, 8192, 3, 12, 5, 999, 2,
                            "hit", 4, "ok", "")
assert_true(load_receipt_check_against_plan(p, r).ok)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/startup/load_plan_receipt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering load plan sealing, a conforming load produces a matching receipt.
- load plan sealing
- a conforming load produces a matching receipt

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

- Canonical SPipe generation for source `b5aa4f26a88b5212ad8b3bed851059e478017c40e2222b233ae2e226095c57b4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b5aa4f26a88b5212ad8b3bed851059e478017c40e2222b233ae2e226095c57b4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b5aa4f26a88b5212ad8b3bed851059e478017c40e2222b233ae2e226095c57b4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/startup/load_plan_receipt_spec.spl
mirror: doc/06_spec/01_unit/app/startup/load_plan_receipt_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/startup/load_plan_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/startup/load_plan_receipt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/startup/load_plan_receipt_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'seals a plan with a non-empty stable hash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/load_plan_receipt_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders SDN with header and plan_hash row' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/load_plan_receipt_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'receipt recorded with the planned counts checks GREEN' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
