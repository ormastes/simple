# Cos Approx Parity Specification

> Tests covering cos_approx canonical impl, sin_approx canonical impl, Identity sin^2 + cos^2 = 1 (former-stub call sites are now real).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cos Approx Parity Specification

## Scenarios

### cos_approx canonical impl

#### Taylor-series correctness

#### cos(0) = 1.0

- cos(0) = 1.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cos(0) = 1.0")
val r = cos_approx(0.0)
expect r == 1.0
```

</details>

#### cos(PI) is approximately -1.0

- cos(PI) is approximately -1.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cos(PI) is approximately -1.0")
val r = cos_approx(PI)
val diff = r - (0.0 - 1.0)
val abs_diff = if diff < 0.0: 0.0 - diff else: diff
expect abs_diff < 0.000001
```

</details>

#### cos(PI/2) is approximately 0.0

- cos(PI/2) is approximately 0.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cos(PI/2) is approximately 0.0")
val r = cos_approx(PI / 2.0)
val abs_r = if r < 0.0: 0.0 - r else: r
expect abs_r < 0.000001
```

</details>

### sin_approx canonical impl

#### Taylor-series correctness

#### sin(0) = 0.0

- sin(0) = 0.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sin(0) = 0.0")
val r = sin_approx(0.0)
expect r == 0.0
```

</details>

#### sin(PI/2) is approximately 1.0

- sin(PI/2) is approximately 1.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sin(PI/2) is approximately 1.0")
val r = sin_approx(PI / 2.0)
val diff = r - 1.0
val abs_diff = if diff < 0.0: 0.0 - diff else: diff
expect abs_diff < 0.000001
```

</details>

### Identity sin^2 + cos^2 = 1 (former-stub call sites are now real)

#### Pythagorean identity

#### holds at PI/4

- holds at PI/4


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("holds at PI/4")
val s = sin_approx(PI / 4.0)
val c = cos_approx(PI / 4.0)
val sum = s * s + c * c
val abs_diff = if sum > 1.0: sum - 1.0 else: 1.0 - sum
expect abs_diff < 0.000001
```

</details>

#### holds at PI/3

- holds at PI/3


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("holds at PI/3")
val s = sin_approx(PI / 3.0)
val c = cos_approx(PI / 3.0)
val sum = s * s + c * c
val abs_diff = if sum > 1.0: sum - 1.0 else: 1.0 - sum
expect abs_diff < 0.000001
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/complex/cos_approx_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering cos_approx canonical impl, sin_approx canonical impl, Identity sin^2 + cos^2 = 1 (former-stub call sites are now real).
- cos_approx canonical impl
- sin_approx canonical impl
- Identity sin^2 + cos^2 = 1 (former-stub call sites are now real)

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `08d9cf58abd94e1d12918e369cb71c69620bbd1f03c710e2ef25c4dadcc01b1c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `08d9cf58abd94e1d12918e369cb71c69620bbd1f03c710e2ef25c4dadcc01b1c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `08d9cf58abd94e1d12918e369cb71c69620bbd1f03c710e2ef25c4dadcc01b1c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/complex/cos_approx_parity_spec.spl
mirror: doc/06_spec/unit/lib/common/complex/cos_approx_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/complex/cos_approx_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/complex/cos_approx_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/complex/cos_approx_parity_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cos(0) = 1.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/complex/cos_approx_parity_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cos(PI) is approximately -1.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/complex/cos_approx_parity_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cos(PI/2) is approximately 0.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
