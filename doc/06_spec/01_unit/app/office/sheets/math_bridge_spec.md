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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = excel_sin(1.570796327)  # π/2
assert_true(result > 0.999999 and result < 1.000001)
```

</details>

#### COS computes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = excel_cos(0.0)
assert_true(result > 0.999999 and result < 1.000001)
```

</details>

#### EXP computes e^1 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = excel_exp(1.0)
assert_true(result > 2.71828 and result < 2.71829)
```

</details>

#### LN computes natural log

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = excel_ln(2.718281828)
assert_true(result > 0.999999 and result < 1.000001)
```

</details>

#### SQRT computes square root

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = excel_sqrt(4.0)
assert_equal(result, 2.0)
```

</details>

#### SUM aggregates array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [f64] = [1.0, 2.0, 3.0, 4.0]
assert_equal(excel_sum(arr), 10.0)
```

</details>

#### AVERAGE computes mean

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [f64] = [1.0, 2.0, 3.0, 4.0]
assert_equal(excel_average(arr), 2.5)
```

</details>

#### COUNT returns array length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [f64] = [1.0, 2.0, 3.0, 4.0]
assert_equal(excel_count(arr), 4)
```

</details>

#### MIN finds minimum

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [f64] = [3.0, 1.0, 4.0, 2.0]
assert_equal(excel_min(arr), 1.0)
```

</details>

#### MAX finds maximum

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [f64] = [3.0, 1.0, 4.0, 2.0]
assert_equal(excel_max(arr), 4.0)
```

</details>

#### PRODUCT multiplies values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [f64] = [2.0, 3.0, 4.0]
assert_equal(excel_product(arr), 24.0)
```

</details>

#### SUMSQ sums squares

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [f64] = [1.0, 2.0, 3.0]
assert_equal(excel_sumsq(arr), 14.0)  # 1 + 4 + 9
```

</details>

#### EMPTY array handling

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [f64] = []
assert_equal(excel_sum(empty), 0.0)
assert_equal(excel_product(empty), 1.0)
```

</details>

#### DEGREES converts radians to degrees

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = excel_degrees(3.141592654)
assert_true(result > 179.999 and result < 180.001)
```

</details>

#### RADIANS converts degrees to radians

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-08-18 |
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
