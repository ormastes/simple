# Math Bridge Working Specification

> Tests covering Math Bridge Migration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Bridge Working Specification

## Scenarios

### Math Bridge Migration

#### SIN basic test

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- SIN basic test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SIN basic test")
val result = excel_sin(1.570796327)  # π/2
assert_true(result > 0.9 and result < 1.1)
```

</details>

#### COS basic test

- COS basic test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("COS basic test")
val result = excel_cos(0.0)
assert_true(result > 0.9 and result < 1.1)
```

</details>

#### TAN basic test

- TAN basic test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TAN basic test")
val result = excel_tan(0.785398163)  # π/4
assert_true(result > 0.9 and result < 1.1)
```

</details>

#### EXP basic test

- EXP basic test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EXP basic test")
val result = excel_exp(1.0)  # e^1
assert_true(result > 2.7 and result < 2.72)
```

</details>

#### LN basic test

- LN basic test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LN basic test")
val result = excel_ln(2.718281828)  # ln(e)
assert_true(result > 0.9 and result < 1.1)
```

</details>

#### SQRT basic test

- SQRT basic test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SQRT basic test")
assert_equal(excel_sqrt(4.0), 2.0)
assert_equal(excel_sqrt(9.0), 3.0)
```

</details>

#### LOG10 basic test

- LOG10 basic test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LOG10 basic test")
val result = excel_log10(10.0)
assert_true(result > 0.9 and result < 1.1)
```

</details>

#### LOG with base test

- LOG with base test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LOG with base test")
val result = excel_log(8.0, 2.0)  # log₂(8) = 3
assert_true(result > 2.9 and result < 3.1)
```

</details>

#### SQRTPI test

- SQRTPI test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SQRTPI test")
val result = excel_sqrt_pi(1.0)  # √π
assert_true(result > 1.77 and result < 1.78)
```

</details>

#### SINH test

- SINH test


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SINH test")
val x = 1.0
val result = excel_sinh(x)
assert_true(result > 1.17 and result < 1.18)  # (e - e^-1) / 2 ≈ 1.175
```

</details>

#### COSH test

- COSH test


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("COSH test")
val x = 1.0
val result = excel_cosh(x)
assert_true(result > 1.54 and result < 1.55)  # (e + e^-1) / 2 ≈ 1.543
```

</details>

#### TANH test

- TANH test


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TANH test")
assert_equal(excel_tanh(0.0), 0.0)
val tanh1 = excel_tanh(1.0)
assert_true(tanh1 > 0.76 and tanh1 < 0.762)
```

</details>

#### SUM array test

- SUM array test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SUM array test")
val arr: [f64] = [1.0, 2.0, 3.0, 4.0]
assert_equal(excel_sum(arr), 10.0)
```

</details>

#### AVERAGE array test

- AVERAGE array test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AVERAGE array test")
val arr: [f64] = [2.0, 4.0, 6.0]
assert_equal(excel_average(arr), 4.0)
```

</details>

#### COUNT test

- COUNT test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("COUNT test")
val arr: [f64] = [1.0, 2.0, 3.0, 4.0]
assert_equal(excel_count(arr), 4)
```

</details>

#### MIN test

- MIN test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MIN test")
val arr: [f64] = [5.0, 2.0, 8.0, 1.0]
assert_equal(excel_min(arr), 1.0)
```

</details>

#### MAX test

- MAX test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MAX test")
val arr: [f64] = [5.0, 2.0, 8.0, 1.0]
assert_equal(excel_max(arr), 8.0)
```

</details>

#### PRODUCT test

- PRODUCT test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PRODUCT test")
val arr: [f64] = [2.0, 3.0, 4.0]
assert_equal(excel_product(arr), 24.0)
```

</details>

#### SUMSQ test

- SUMSQ test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SUMSQ test")
val arr: [f64] = [1.0, 2.0, 3.0]
assert_equal(excel_sumsq(arr), 14.0)  # 1 + 4 + 9
```

</details>

#### Empty array handling

- Empty array handling


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Empty array handling")
val empty: [f64] = []
assert_equal(excel_sum(empty), 0.0)
assert_equal(excel_product(empty), 1.0)
assert_equal(excel_count(empty), 0)
```

</details>

#### Single element arrays

- Single element arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Single element arrays")
val single: [f64] = [5.0]
assert_equal(excel_sum(single), 5.0)
assert_equal(excel_average(single), 5.0)
assert_equal(excel_min(single), 5.0)
assert_equal(excel_max(single), 5.0)
```

</details>

#### Negative numbers in aggregates

- Negative numbers in aggregates


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Negative numbers in aggregates")
val neg: [f64] = [-1.0, -2.0, -3.0]
assert_equal(excel_sum(neg), -6.0)
```

</details>

#### Mixed positive and negative

- Mixed positive and negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Mixed positive and negative")
val mixed: [f64] = [-5.0, 10.0, -3.0, 8.0]
assert_equal(excel_sum(mixed), 10.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/math_bridge_working_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Math Bridge Migration.
- Math Bridge Migration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
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

- Canonical SPipe generation for source `c4fc9caa846b7273d8f683f63099a38f3ab735d1a64cf8916a3f83974359f955`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c4fc9caa846b7273d8f683f63099a38f3ab735d1a64cf8916a3f83974359f955`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c4fc9caa846b7273d8f683f63099a38f3ab735d1a64cf8916a3f83974359f955`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/math_bridge_working_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/math_bridge_working_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/math_bridge_working_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/math_bridge_working_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/math_bridge_working_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SIN basic test' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/math_bridge_working_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'COS basic test' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/math_bridge_working_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TAN basic test' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
