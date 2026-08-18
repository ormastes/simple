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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = excel_sin(1.570796327)  # π/2
assert_true(result > 0.9 and result < 1.1)
```

</details>

#### COS basic test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = excel_cos(0.0)
assert_true(result > 0.9 and result < 1.1)
```

</details>

#### TAN basic test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = excel_tan(0.785398163)  # π/4
assert_true(result > 0.9 and result < 1.1)
```

</details>

#### EXP basic test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = excel_exp(1.0)  # e^1
assert_true(result > 2.7 and result < 2.72)
```

</details>

#### LN basic test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = excel_ln(2.718281828)  # ln(e)
assert_true(result > 0.9 and result < 1.1)
```

</details>

#### SQRT basic test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(excel_sqrt(4.0), 2.0)
assert_equal(excel_sqrt(9.0), 3.0)
```

</details>

#### LOG10 basic test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = excel_log10(10.0)
assert_true(result > 0.9 and result < 1.1)
```

</details>

#### LOG with base test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = excel_log(8.0, 2.0)  # log₂(8) = 3
assert_true(result > 2.9 and result < 3.1)
```

</details>

#### SQRTPI test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = excel_sqrt_pi(1.0)  # √π
assert_true(result > 1.77 and result < 1.78)
```

</details>

#### SINH test

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1.0
val result = excel_sinh(x)
assert_true(result > 1.17 and result < 1.18)  # (e - e^-1) / 2 ≈ 1.175
```

</details>

#### COSH test

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1.0
val result = excel_cosh(x)
assert_true(result > 1.54 and result < 1.55)  # (e + e^-1) / 2 ≈ 1.543
```

</details>

#### TANH test

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(excel_tanh(0.0), 0.0)
val tanh1 = excel_tanh(1.0)
assert_true(tanh1 > 0.76 and tanh1 < 0.762)
```

</details>

#### SUM array test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [f64] = [1.0, 2.0, 3.0, 4.0]
assert_equal(excel_sum(arr), 10.0)
```

</details>

#### AVERAGE array test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [f64] = [2.0, 4.0, 6.0]
assert_equal(excel_average(arr), 4.0)
```

</details>

#### COUNT test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [f64] = [1.0, 2.0, 3.0, 4.0]
assert_equal(excel_count(arr), 4)
```

</details>

#### MIN test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [f64] = [5.0, 2.0, 8.0, 1.0]
assert_equal(excel_min(arr), 1.0)
```

</details>

#### MAX test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [f64] = [5.0, 2.0, 8.0, 1.0]
assert_equal(excel_max(arr), 8.0)
```

</details>

#### PRODUCT test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [f64] = [2.0, 3.0, 4.0]
assert_equal(excel_product(arr), 24.0)
```

</details>

#### SUMSQ test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [f64] = [1.0, 2.0, 3.0]
assert_equal(excel_sumsq(arr), 14.0)  # 1 + 4 + 9
```

</details>

#### Empty array handling

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [f64] = []
assert_equal(excel_sum(empty), 0.0)
assert_equal(excel_product(empty), 1.0)
assert_equal(excel_count(empty), 0)
```

</details>

#### Single element arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val single: [f64] = [5.0]
assert_equal(excel_sum(single), 5.0)
assert_equal(excel_average(single), 5.0)
assert_equal(excel_min(single), 5.0)
assert_equal(excel_max(single), 5.0)
```

</details>

#### Negative numbers in aggregates

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val neg: [f64] = [-1.0, -2.0, -3.0]
assert_equal(excel_sum(neg), -6.0)
```

</details>

#### Mixed positive and negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-08-18 |
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
