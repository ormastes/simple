# Math Bridge Significance Sign Class Specification

> Tests covering Rounding-to-significance: step sign must not be observable.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Bridge Significance Sign Class Specification

## Scenarios

### Rounding-to-significance: step sign must not be observable

#### FLOOR is invariant under negating the significance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- FLOOR is invariant under negating the significance


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FLOOR is invariant under negating the significance")
# Every pair must agree; the sign of the step carries no information.
assert_equal(excel_floor(10.0, 3.0), excel_floor(10.0, -3.0))
assert_equal(excel_floor(-10.0, 3.0), excel_floor(-10.0, -3.0))
assert_equal(excel_floor(3.7, 1.0), excel_floor(3.7, -1.0))
assert_equal(excel_floor(-3.7, 1.0), excel_floor(-3.7, -1.0))
assert_equal(excel_floor(0.0, 5.0), excel_floor(0.0, -5.0))
assert_equal(excel_floor(7.25, 0.5), excel_floor(7.25, -0.5))
```

</details>

#### CEILING is invariant under negating the significance

- CEILING is invariant under negating the significance


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CEILING is invariant under negating the significance")
assert_equal(excel_ceiling(10.0, 3.0), excel_ceiling(10.0, -3.0))
assert_equal(excel_ceiling(-10.0, 3.0), excel_ceiling(-10.0, -3.0))
assert_equal(excel_ceiling(3.2, 1.0), excel_ceiling(3.2, -1.0))
assert_equal(excel_ceiling(-3.2, 1.0), excel_ceiling(-3.2, -1.0))
assert_equal(excel_ceiling(0.0, 5.0), excel_ceiling(0.0, -5.0))
assert_equal(excel_ceiling(7.25, 0.5), excel_ceiling(7.25, -0.5))
```

</details>

#### FLOOR never rounds away from zero-ward direction under a negative step

- FLOOR never rounds away from zero-ward direction under a negative step


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FLOOR never rounds away from zero-ward direction under a negative step")
# Direction check, independent of the invariant above: FLOOR must never
# exceed its input. A raw-signed divide makes FLOOR(10, -3) = 12 > 10.
assert_true(excel_floor(10.0, -3.0) <= 10.0)
assert_true(excel_floor(3.7, -1.0) <= 3.7)
assert_true(excel_floor(-3.7, -1.0) <= -3.7)
assert_true(excel_floor(100.0, -7.0) <= 100.0)
```

</details>

#### CEILING never falls below its input under a negative step

- CEILING never falls below its input under a negative step


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CEILING never falls below its input under a negative step")
# A raw-signed divide makes CEILING(10, -3) = 9 < 10.
assert_true(excel_ceiling(10.0, -3.0) >= 10.0)
assert_true(excel_ceiling(3.2, -1.0) >= 3.2)
assert_true(excel_ceiling(-3.2, -1.0) >= -3.2)
assert_true(excel_ceiling(100.0, -7.0) >= 100.0)
```

</details>

#### FLOOR and CEILING bracket the input for either step sign

- FLOOR and CEILING bracket the input for either step sign


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FLOOR and CEILING bracket the input for either step sign")
# The pair must always straddle x, whichever sign the step is given in.
assert_true(excel_floor(41.0, 6.0) <= 41.0)
assert_true(excel_ceiling(41.0, 6.0) >= 41.0)
assert_true(excel_floor(41.0, -6.0) <= 41.0)
assert_true(excel_ceiling(41.0, -6.0) >= 41.0)
assert_true(excel_floor(-41.0, -6.0) <= -41.0)
assert_true(excel_ceiling(-41.0, -6.0) >= -41.0)
```

</details>

#### zero significance stays the documented degenerate case for both signs

- zero significance stays the documented degenerate case for both signs


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero significance stays the documented degenerate case for both signs")
# Guard the early-return so a sign fix cannot accidentally divide by zero.
assert_equal(excel_floor(5.5, 0.0), 0.0)
assert_equal(excel_ceiling(5.5, 0.0), 0.0)
assert_equal(excel_floor(-5.5, 0.0), 0.0)
assert_equal(excel_ceiling(-5.5, 0.0), 0.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/math_bridge_significance_sign_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Rounding-to-significance: step sign must not be observable.
- Rounding-to-significance: step sign must not be observable

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `5f1268bcd065ac4e514222f37f597be7ff6ac4e6d91ad05ee2e2c5046c771e34`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5f1268bcd065ac4e514222f37f597be7ff6ac4e6d91ad05ee2e2c5046c771e34`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5f1268bcd065ac4e514222f37f597be7ff6ac4e6d91ad05ee2e2c5046c771e34`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/math_bridge_significance_sign_class_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/math_bridge_significance_sign_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/math_bridge_significance_sign_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/math_bridge_significance_sign_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/math_bridge_significance_sign_class_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FLOOR is invariant under negating the significance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/math_bridge_significance_sign_class_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CEILING is invariant under negating the significance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/math_bridge_significance_sign_class_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FLOOR never rounds away from zero-ward direction under a negative step' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
