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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(excel_ceiling(10.0, 3.0), excel_ceiling(10.0, -3.0))
assert_equal(excel_ceiling(-10.0, 3.0), excel_ceiling(-10.0, -3.0))
assert_equal(excel_ceiling(3.2, 1.0), excel_ceiling(3.2, -1.0))
assert_equal(excel_ceiling(-3.2, 1.0), excel_ceiling(-3.2, -1.0))
assert_equal(excel_ceiling(0.0, 5.0), excel_ceiling(0.0, -5.0))
assert_equal(excel_ceiling(7.25, 0.5), excel_ceiling(7.25, -0.5))
```

</details>

#### FLOOR never rounds away from zero-ward direction under a negative step

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Direction check, independent of the invariant above: FLOOR must never
# exceed its input. A raw-signed divide makes FLOOR(10, -3) = 12 > 10.
assert_true(excel_floor(10.0, -3.0) <= 10.0)
assert_true(excel_floor(3.7, -1.0) <= 3.7)
assert_true(excel_floor(-3.7, -1.0) <= -3.7)
assert_true(excel_floor(100.0, -7.0) <= 100.0)
```

</details>

#### CEILING never falls below its input under a negative step

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A raw-signed divide makes CEILING(10, -3) = 9 < 10.
assert_true(excel_ceiling(10.0, -3.0) >= 10.0)
assert_true(excel_ceiling(3.2, -1.0) >= 3.2)
assert_true(excel_ceiling(-3.2, -1.0) >= -3.2)
assert_true(excel_ceiling(100.0, -7.0) >= 100.0)
```

</details>

#### FLOOR and CEILING bracket the input for either step sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-08-18 |
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
