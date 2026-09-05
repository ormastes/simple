# Math Bridge Extended Specification

> Tests covering Extended Math Bridge - HIGH PRIORITY Functions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Bridge Extended Specification

## Scenarios

### Extended Math Bridge - HIGH PRIORITY Functions

#### POWER computes base^exp

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- POWER computes base^exp


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("POWER computes base^exp")
assert_equal(excel_power(2.0, 3.0), 8.0)  # 2³ = 8
assert_equal(excel_power(5.0, 2.0), 25.0)  # 5² = 25
assert_equal(excel_power(10.0, 0.0), 1.0)   # 10⁰ = 1
assert_equal(excel_power(3.0, 1.0), 3.0)    # 3¹ = 3
```

</details>

#### POWER handles negative exponents

- POWER handles negative exponents


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("POWER handles negative exponents")
val result = excel_power(2.0, -2.0)  # 2⁻² = 0.25
assert_true(result > 0.24 and result < 0.26)
```

</details>

#### ABS returns absolute value

- ABS returns absolute value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ABS returns absolute value")
assert_equal(excel_abs(5.0), 5.0)
assert_equal(excel_abs(-5.0), 5.0)
assert_equal(excel_abs(0.0), 0.0)
assert_equal(excel_abs(-3.14), 3.14)
```

</details>

#### ROUND rounds to specified digits

- ROUND rounds to specified digits


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ROUND rounds to specified digits")
assert_equal(excel_round(3.14159, 2), 3.14)
assert_equal(excel_round(3.14159, 3), 3.142)
assert_equal(excel_round(1234.56, -2), 1200.0)  # Round to hundreds
assert_equal(excel_round(2.5, 0), 3.0)  # Round half away from zero
```

</details>

#### ROUND handles negative numbers

- ROUND handles negative numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ROUND handles negative numbers")
assert_equal(excel_round(-2.5, 0), -3.0)
assert_equal(excel_round(-3.14, 1), -3.1)
```

</details>

#### TRUNC truncates to specified digits

- TRUNC truncates to specified digits


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TRUNC truncates to specified digits")
assert_equal(excel_trunc(3.14159, 2), 3.14)
assert_equal(excel_trunc(3.999, 0), 3.0)
assert_equal(excel_trunc(-3.999, 0), -3.0)
assert_equal(excel_trunc(1234.56, -2), 1200.0)
```

</details>

#### TRUNC always toward zero

- TRUNC always toward zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TRUNC always toward zero")
assert_equal(excel_trunc(2.9, 0), 2.0)
assert_equal(excel_trunc(-2.9, 0), -2.0)
```

</details>

#### VAR.P computes population variance

- VAR.P computes population variance


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VAR.P computes population variance")
val data: [f64] = [1.0, 2.0, 3.0, 4.0, 5.0]
# Mean = 3, Var = ((1-3)² + (2-3)² + (3-3)² + (4-3)² + (5-3)²) / 5
# = (4 + 1 + 0 + 1 + 4) / 5 = 10/5 = 2.0
assert_equal(excel_var_p(data), 2.0)
```

</details>

#### STDEV.P computes population standard deviation

- STDEV.P computes population standard deviation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("STDEV.P computes population standard deviation")
val data: [f64] = [1.0, 2.0, 3.0, 4.0, 5.0]
# STDEV.P = √VAR.P = √2.0 ≈ 1.414
val result = excel_stdev_p(data)
assert_true(result > 1.41 and result < 1.42)
```

</details>

#### VAR.P handles single element

- VAR.P handles single element


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VAR.P handles single element")
val single: [f64] = [5.0]
# Variance of single element = 0
assert_equal(excel_var_p(single), 0.0)
```

</details>

#### STDEV.P handles single element

- STDEV.P handles single element


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("STDEV.P handles single element")
val single: [f64] = [5.0]
# STDEV of single element = 0
assert_equal(excel_stdev_p(single), 0.0)
```

</details>

#### VAR.P handles empty array

- VAR.P handles empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VAR.P handles empty array")
val empty: [f64] = []
# Should return 0.0 for empty (Excel returns #DIV/0! but we handle gracefully)
assert_equal(excel_var_p(empty), 0.0)
```

</details>

#### STDEV.P handles empty array

- STDEV.P handles empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("STDEV.P handles empty array")
val empty: [f64] = []
assert_equal(excel_stdev_p(empty), 0.0)
```

</details>

#### POWER with fractional exponents

- POWER with fractional exponents


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("POWER with fractional exponents")
val result = excel_power(9.0, 0.5)  # √9 = 3
assert_true(result > 2.99 and result < 3.01)
```

</details>

#### POWER with base 0

- POWER with base 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("POWER with base 0")
assert_equal(excel_power(0.0, 5.0), 0.0)  # 0⁵ = 0
assert_equal(excel_power(5.0, 0.0), 1.0)   # 5⁰ = 1
```

</details>

#### ROUND with zero digits rounds to integer

- ROUND with zero digits rounds to integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ROUND with zero digits rounds to integer")
assert_equal(excel_round(3.7, 0), 4.0)
assert_equal(excel_round(3.2, 0), 3.0)
assert_equal(excel_round(-3.7, 0), -4.0)
```

</details>

#### TRUNC with zero digits truncates to integer

- TRUNC with zero digits truncates to integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TRUNC with zero digits truncates to integer")
assert_equal(excel_trunc(3.9, 0), 3.0)
assert_equal(excel_trunc(-3.9, 0), -3.0)
```

</details>

#### FLOOR rounds down to significance

- FLOOR rounds down to significance


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FLOOR rounds down to significance")
assert_equal(excel_floor(3.7, 1), 3.0)
assert_equal(excel_floor(3.7, 2), 2.0)
assert_equal(excel_floor(-3.7, -1), -4.0)
```

</details>

#### CEILING rounds up to significance

- CEILING rounds up to significance


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CEILING rounds up to significance")
assert_equal(excel_ceiling(3.2, 1), 4.0)
assert_equal(excel_ceiling(3.2, 2), 4.0)
assert_equal(excel_ceiling(-3.2, -1), -3.0)
```

</details>

#### FLOOR with zero significance returns zero

- FLOOR with zero significance returns zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FLOOR with zero significance returns zero")
assert_equal(excel_floor(5.5, 0.0), 0.0)
```

</details>

#### CEILING with zero significance returns zero

- CEILING with zero significance returns zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CEILING with zero significance returns zero")
assert_equal(excel_ceiling(5.5, 0.0), 0.0)
```

</details>

#### FLOOR handles negative significance

- FLOOR handles negative significance


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FLOOR handles negative significance")
assert_equal(excel_floor(10.0, -3), 9.0)
assert_equal(excel_floor(-10.0, 3), -12.0)
```

</details>

#### CEILING handles negative significance

- CEILING handles negative significance


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CEILING handles negative significance")
assert_equal(excel_ceiling(10.0, -3), 12.0)
assert_equal(excel_ceiling(-10.0, 3), -9.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/math_bridge_extended_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Extended Math Bridge - HIGH PRIORITY Functions.
- Extended Math Bridge - HIGH PRIORITY Functions

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

- Canonical SPipe generation for source `683024ba65280e6236e16c4647a5678ed39598d02904f093c797966f9e73b17d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `683024ba65280e6236e16c4647a5678ed39598d02904f093c797966f9e73b17d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `683024ba65280e6236e16c4647a5678ed39598d02904f093c797966f9e73b17d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/math_bridge_extended_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/math_bridge_extended_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/math_bridge_extended_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/math_bridge_extended_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/math_bridge_extended_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'POWER computes base^exp' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/math_bridge_extended_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'POWER handles negative exponents' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/math_bridge_extended_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ABS returns absolute value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
