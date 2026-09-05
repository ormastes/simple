# Lr Warmup Linear Negative After Total Steps Specification

> Tests covering lr_warmup_linear.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lr Warmup Linear Negative After Total Steps Specification

## Scenarios

### lr_warmup_linear

#### does not go negative once step exceeds total_steps

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not go negative once step exceeds total_steps


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not go negative once step exceeds total_steps")
val lr = lr_warmup_linear(20, 2, 10, 1.0)
expect(lr).to_be_greater_than(-0.0000001)
```

</details>

#### returns base_lr at the end of warmup

- returns base_lr at the end of warmup
   - Expected: lr equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns base_lr at the end of warmup")
val lr = lr_warmup_linear(2, 2, 10, 1.0)
expect(lr).to_equal(1.0)
```

</details>

#### decays linearly to 0 at total_steps

- decays linearly to 0 at total_steps
   - Expected: lr equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decays linearly to 0 at total_steps")
val lr = lr_warmup_linear(10, 2, 10, 1.0)
expect(lr).to_equal(0.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/torch/lr_warmup_linear_negative_after_total_steps_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering lr_warmup_linear.
- lr_warmup_linear

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `51ab58b3cecf3545ef9593fb27d61c449d57a9122a45d6d9899a14c1d06803a9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `51ab58b3cecf3545ef9593fb27d61c449d57a9122a45d6d9899a14c1d06803a9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `51ab58b3cecf3545ef9593fb27d61c449d57a9122a45d6d9899a14c1d06803a9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/torch/lr_warmup_linear_negative_after_total_steps_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/torch/lr_warmup_linear_negative_after_total_steps_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/torch/lr_warmup_linear_negative_after_total_steps_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/torch/lr_warmup_linear_negative_after_total_steps_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/torch/lr_warmup_linear_negative_after_total_steps_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/torch/lr_warmup_linear_negative_after_total_steps_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not go negative once step exceeds total_steps' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/torch/lr_warmup_linear_negative_after_total_steps_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns base_lr at the end of warmup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/torch/lr_warmup_linear_negative_after_total_steps_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decays linearly to 0 at total_steps' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
