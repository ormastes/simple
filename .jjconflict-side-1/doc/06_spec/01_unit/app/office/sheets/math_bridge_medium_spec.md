# Math Bridge Medium Specification

> Tests covering Medium Priority Excel Functions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Bridge Medium Specification

## Scenarios

### Medium Priority Excel Functions

#### ATAN2 computes correct quadrant

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ATAN2 computes correct quadrant


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ATAN2 computes correct quadrant")
# Quadrant I: x>0, y>0
val q1 = excel_atan2(1.0, 1.0)
assert_true(q1 > 0.78 and q1 < 0.79)  # π/4 ≈ 0.785

# Quadrant II: x<0, y>0
val q2 = excel_atan2(1.0, -1.0)
assert_true(q2 > 2.35 and q2 < 2.36)  # 3π/4 ≈ 2.356

# Quadrant III: x<0, y<0
val q3 = excel_atan2(-1.0, -1.0)
assert_true(q3 > -2.36 and q3 < -2.35)  # -3π/4 ≈ -2.356

# Quadrant IV: x>0, y<0
val q4 = excel_atan2(-1.0, 1.0)
assert_true(q4 > -0.79 and q4 < -0.78)  # -π/4 ≈ -0.785
```

</details>

#### ATAN2 handles axis cases

- ATAN2 handles axis cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ATAN2 handles axis cases")
# Positive Y axis
assert_true(excel_atan2(1.0, 0.0) > 1.57 and excel_atan2(1.0, 0.0) < 1.58)  # π/2

# Negative Y axis
assert_true(excel_atan2(-1.0, 0.0) > -1.58 and excel_atan2(-1.0, 0.0) < -1.57)  # -π/2

# Positive X axis
assert_true(excel_atan2(0.0, 1.0) > -0.01 and excel_atan2(0.0, 1.0) < 0.01)  # 0

# Negative X axis
val pi = excel_atan2(0.0, -1.0)
assert_true(pi > 3.13 and pi < 3.15)  # π
```

</details>

#### STANDARDIZE computes z-score

- STANDARDIZE computes z-score


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("STANDARDIZE computes z-score")
# (x - mean) / stdev
val z1 = excel_standardize(90.0, 80.0, 10.0)  # (90-80)/10 = 1.0
assert_true(z1 > 0.99 and z1 < 1.01)

val z2 = excel_standardize(70.0, 80.0, 10.0)  # (70-80)/10 = -1.0
assert_true(z2 > -1.01 and z2 < -0.99)

val z3 = excel_standardize(80.0, 80.0, 10.0)  # (80-80)/10 = 0.0
assert_true(z3 > -0.01 and z3 < 0.01)
```

</details>

#### STANDARDIZE handles decimal inputs

- STANDARDIZE handles decimal inputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("STANDARDIZE handles decimal inputs")
val z = excel_standardize(85.5, 80.0, 5.0)  # (85.5-80)/5 = 1.1
assert_true(z > 1.09 and z < 1.11)
```

</details>

#### STANDARDIZE with negative mean

- STANDARDIZE with negative mean


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("STANDARDIZE with negative mean")
val z = excel_standardize(-10.0, -20.0, 10.0)  # (-10 - (-20))/10 = 1.0
assert_true(z > 0.99 and z < 1.01)
```

</details>

#### ATAN2 with equal coordinates

- ATAN2 with equal coordinates


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ATAN2 with equal coordinates")
# 45 degrees in all quadrants
assert_true(excel_atan2(1.0, 1.0) > 0.78 and excel_atan2(1.0, 1.0) < 0.79)
assert_true(excel_atan2(-1.0, 1.0) > -0.79 and excel_atan2(-1.0, 1.0) < -0.78)
assert_true(excel_atan2(-1.0, -1.0) > -2.36 and excel_atan2(-1.0, -1.0) < -2.35)
assert_true(excel_atan2(1.0, -1.0) > 2.35 and excel_atan2(1.0, -1.0) < 2.36)
```

</details>

#### STANDARDIZE with very small stdev

- STANDARDIZE with very small stdev


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("STANDARDIZE with very small stdev")
# (100-90)/0.01 = 1000
val z = excel_standardize(100.0, 90.0, 0.01)
assert_true(z > 999.0 and z < 1001.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/math_bridge_medium_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Medium Priority Excel Functions.
- Medium Priority Excel Functions

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

- Canonical SPipe generation for source `1a8d04bb935b3199918c7c20412876128565abe9bfaeb9d0fcade51381de5599`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1a8d04bb935b3199918c7c20412876128565abe9bfaeb9d0fcade51381de5599`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1a8d04bb935b3199918c7c20412876128565abe9bfaeb9d0fcade51381de5599`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/math_bridge_medium_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/math_bridge_medium_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/math_bridge_medium_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/math_bridge_medium_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/math_bridge_medium_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ATAN2 computes correct quadrant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/math_bridge_medium_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ATAN2 handles axis cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/math_bridge_medium_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'STANDARDIZE computes z-score' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
