# Math Bridge Specification

> Tests covering Math Bridge Functions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Bridge Specification

## Scenarios

### Math Bridge Functions

#### SIN computes correctly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- SIN computes correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SIN computes correctly")
val result = excel_sin(1.570796327)  # π/2
assert_true(result > 0.999999 and result < 1.000001)
```

</details>

#### COS computes correctly

- COS computes correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("COS computes correctly")
val result = excel_cos(0.0)
assert_true(result > 0.999999 and result < 1.000001)
```

</details>

#### EXP computes e^1 correctly

- EXP computes e^1 correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EXP computes e^1 correctly")
val result = excel_exp(1.0)
assert_true(result > 2.71828 and result < 2.71829)
```

</details>

#### LN computes natural log

- LN computes natural log


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LN computes natural log")
val result = excel_ln(2.718281828)
assert_true(result > 0.999999 and result < 1.000001)
```

</details>

#### SQRT computes square root

- SQRT computes square root


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SQRT computes square root")
val result = excel_sqrt(4.0)
assert_equal(result, 2.0)
```

</details>

#### SUM aggregates array

- SUM aggregates array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SUM aggregates array")
val arr: [f64] = [1.0, 2.0, 3.0, 4.0]
assert_equal(excel_sum(arr), 10.0)
```

</details>

#### AVERAGE computes mean

- AVERAGE computes mean


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AVERAGE computes mean")
val arr: [f64] = [1.0, 2.0, 3.0, 4.0]
assert_equal(excel_average(arr), 2.5)
```

</details>

#### COUNT returns array length

- COUNT returns array length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("COUNT returns array length")
val arr: [f64] = [1.0, 2.0, 3.0, 4.0]
assert_equal(excel_count(arr), 4)
```

</details>

#### MIN finds minimum

- MIN finds minimum


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MIN finds minimum")
val arr: [f64] = [3.0, 1.0, 4.0, 2.0]
assert_equal(excel_min(arr), 1.0)
```

</details>

#### MAX finds maximum

- MAX finds maximum


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MAX finds maximum")
val arr: [f64] = [3.0, 1.0, 4.0, 2.0]
assert_equal(excel_max(arr), 4.0)
```

</details>

#### PRODUCT multiplies values

- PRODUCT multiplies values


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PRODUCT multiplies values")
val arr: [f64] = [2.0, 3.0, 4.0]
assert_equal(excel_product(arr), 24.0)
```

</details>

#### SUMSQ sums squares

- SUMSQ sums squares


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SUMSQ sums squares")
val arr: [f64] = [1.0, 2.0, 3.0]
assert_equal(excel_sumsq(arr), 14.0)  # 1 + 4 + 9
```

</details>

#### EMPTY array handling

- EMPTY array handling


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EMPTY array handling")
val empty: [f64] = []
assert_equal(excel_sum(empty), 0.0)
assert_equal(excel_product(empty), 1.0)
```

</details>

#### DEGREES converts radians to degrees

- DEGREES converts radians to degrees


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DEGREES converts radians to degrees")
val result = excel_degrees(3.141592654)
assert_true(result > 179.999 and result < 180.001)
```

</details>

#### RADIANS converts degrees to radians

- RADIANS converts degrees to radians


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RADIANS converts degrees to radians")
val result = excel_radians(180.0)
assert_true(result > 3.14159 and result < 3.14160)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/math_bridge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Math Bridge Functions.
- Math Bridge Functions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `a4ebd09398d421759111b4374d2a7671df2253701c467336f4cb8cc8a7b51b42`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a4ebd09398d421759111b4374d2a7671df2253701c467336f4cb8cc8a7b51b42`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a4ebd09398d421759111b4374d2a7671df2253701c467336f4cb8cc8a7b51b42`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/math_bridge_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/math_bridge_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/math_bridge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/math_bridge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/math_bridge_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SIN computes correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/math_bridge_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'COS computes correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/math_bridge_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'EXP computes e^1 correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
