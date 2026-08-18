# Math Bridge Comprehensive Specification

> Tests covering Comprehensive Math Bridge Tests, Trigonometry, Logarithmic and Exponential, Statistical Aggregates, Rounding Functions, Angle Conversions, Edge Cases.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Bridge Comprehensive Specification

## Scenarios

### Comprehensive Math Bridge Tests

### Trigonometry

#### SIN with common angles

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sin_0 = excel_sin(0.0)
val sin_pi2 = excel_sin(1.570796327)
val sin_pi = excel_sin(3.141592654)
assert_true(sin_0 > -0.000001 and sin_0 < 0.000001)
assert_true(sin_pi2 > 0.999999 and sin_pi2 < 1.000001)
assert_true(sin_pi > -0.000001 and sin_pi < 0.000001)
```

</details>

#### COS with common angles

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cos_0 = excel_cos(0.0)
val cos_pi2 = excel_cos(1.570796327)
val cos_pi = excel_cos(3.141592654)
assert_true(cos_0 > 0.999999 and cos_0 < 1.000001)
assert_true(cos_pi2 > -0.000001 and cos_pi2 < 0.000001)
assert_true(cos_pi > -1.000001 and cos_pi < -0.999999)
```

</details>

#### TAN computes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tan_0 = excel_tan(0.0)
val tan_pi4 = excel_tan(0.785398163)
assert_true(tan_0 > -0.000001 and tan_0 < 0.000001)
assert_true(tan_pi4 > 0.999999 and tan_pi4 < 1.000001)
```

</details>

#### SINH hyperbolic sine

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1.0
val expected = (2.718281828 - 0.367879441) / 2.0  # (e - e^-1) / 2
val result = excel_sinh(x)
assert_true(result >= expected - 0.0001 and result <= expected + 0.0001)
```

</details>

#### COSH hyperbolic cosine

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1.0
val expected = (2.718281828 + 0.367879441) / 2.0  # (e + e^-1) / 2
assert_true(abs(excel_cosh(x) - expected) < 0.0001)
```

</details>

#### TANH hyperbolic tangent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(excel_tanh(0.0) == 0.0)
assert_true(excel_tanh(1.0) > 0.76 and excel_tanh(1.0) < 0.762)
assert_true(abs(excel_tanh(10.0) - 1.0) < 0.000001)
```

</details>

### Logarithmic and Exponential

#### LN natural logarithm

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(abs(excel_ln(1.0) - 0.0) < 0.000001)
assert_true(abs(excel_ln(2.718281828) - 1.0) < 0.000001)  # ln(e)
assert_true(abs(excel_ln(7.389056099) - 2.0) < 0.000001)  # ln(e²)
```

</details>

#### LOG10 base 10 logarithm

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(abs(excel_log10(1.0) - 0.0) < 0.000001)
assert_true(abs(excel_log10(10.0) - 1.0) < 0.000001)
assert_true(abs(excel_log10(100.0) - 2.0) < 0.000001)
```

</details>

#### LOG with custom base

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(abs(excel_log(8.0, 2.0) - 3.0) < 0.000001)  # log₂(8) = 3
assert_true(abs(excel_log(1000.0, 10.0) - 3.0) < 0.000001)  # log₁₀(1000) = 3
```

</details>

#### EXP exponential e^x

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(abs(excel_exp(0.0) - 1.0) < 0.000001)
assert_true(abs(excel_exp(1.0) - 2.718281828) < 0.0001)
assert_true(abs(excel_exp(2.0) - 7.389056099) < 0.0001)
```

</details>

#### SQRT square root

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(abs(excel_sqrt(0.0) - 0.0) < 0.000001)
assert_true(abs(excel_sqrt(1.0) - 1.0) < 0.000001)
assert_true(abs(excel_sqrt(4.0) - 2.0) < 0.000001)
assert_true(abs(excel_sqrt(9.0) - 3.0) < 0.000001)
```

</details>

#### SQRTPI square root of π*x

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(abs(excel_sqrt_pi(1.0) - 1.772453851) < 0.0001)  # √π
assert_true(abs(excel_sqrt_pi(0.0) - 0.0) < 0.000001)
```

</details>

### Statistical Aggregates

#### SUM adds all values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(excel_sum([1.0, 2.0, 3.0, 4.0]), 10.0)
assert_equal(excel_sum([10.0, -5.0, 3.0]), 8.0)
assert_equal(excel_sum([]), 0.0)
```

</details>

#### AVERAGE computes mean

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(excel_average([2.0, 4.0, 6.0]), 4.0)
assert_equal(excel_average([1.0, 2.0, 3.0, 4.0]), 2.5)
assert_equal(excel_average([10.0, 20.0, 30.0]), 20.0)
```

</details>

#### COUNT returns element count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(excel_count([1.0, 2.0, 3.0]), 3)
assert_equal(excel_count([]), 0)
assert_equal(excel_count([42.0]), 1)
```

</details>

#### MIN finds minimum value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(excel_min([5.0, 2.0, 8.0, 1.0]), 1.0)
assert_equal(excel_min([10.0, 20.0, 30.0]), 10.0)
assert_equal(excel_min([-5.0, 0.0, 5.0]), -5.0)
assert_equal(excel_min([]), 0.0)  # Empty array returns 0
```

</details>

#### MAX finds maximum value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(excel_max([5.0, 2.0, 8.0, 1.0]), 8.0)
assert_equal(excel_max([10.0, 20.0, 30.0]), 30.0)
assert_equal(excel_max([-5.0, 0.0, 5.0]), 5.0)
assert_equal(excel_max([]), 0.0)  # Empty array returns 0
```

</details>

#### PRODUCT multiplies all values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(excel_product([2.0, 3.0, 4.0]), 24.0)
assert_equal(excel_product([1.0, 2.0, 3.0, 4.0]), 24.0)
assert_equal(excel_product([5.0, 6.0]), 30.0)
assert_equal(excel_product([]), 1.0)  # Identity
```

</details>

#### SUMSQ sums squares

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(excel_sumsq([1.0, 2.0, 3.0]), 14.0)  # 1 + 4 + 9
assert_equal(excel_sumsq([3.0, 4.0]), 25.0)  # 9 + 16
assert_equal(excel_sumsq([]), 0.0)
```

</details>

### Rounding Functions

#### ROUNDUP rounds away from zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(excel_roundup(1.2), 2.0)
assert_equal(excel_roundup(1.5), 2.0)
assert_equal(excel_roundup(-1.2), -2.0)
assert_equal(excel_roundup(-1.5), -2.0)
assert_equal(excel_roundup(0.0), 0.0)
```

</details>

#### ROUNDDOWN rounds toward zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(excel_rounddown(1.2), 1.0)
assert_equal(excel_rounddown(1.9), 1.0)
assert_equal(excel_rounddown(-1.2), -1.0)
assert_equal(excel_rounddown(-1.9), -1.0)
assert_equal(excel_rounddown(0.0), 0.0)
```

</details>

#### EVEN rounds up to even integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(excel_even(1.2), 2.0)
assert_equal(excel_even(2.0), 2.0)
assert_equal(excel_even(3.0), 4.0)
assert_equal(excel_even(-1.0), -2.0)
assert_equal(excel_even(-3.0), -4.0)
```

</details>

#### ODD rounds up to odd integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(excel_odd(1.0), 1.0)
assert_equal(excel_odd(2.0), 3.0)
assert_equal(excel_odd(3.0), 3.0)
assert_equal(excel_odd(4.0), 5.0)
assert_equal(excel_odd(-1.0), -1.0)
assert_equal(excel_odd(-2.0), -3.0)
```

</details>

#### MROUND rounds to multiple

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(excel_mround(10.0, 3.0), 9.0)
assert_equal(excel_mround(11.0, 3.0), 12.0)
assert_equal(excel_mround(13.0, 5.0), 15.0)
assert_equal(excel_mround(0.0, 5.0), 0.0)
```

</details>

### Angle Conversions

#### DEGREES converts radians to degrees

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(abs(excel_degrees(0.0) - 0.0) < 0.000001)
assert_true(abs(excel_degrees(1.570796327) - 90.0) < 0.001)  # π/2 = 90°
assert_true(abs(excel_degrees(3.141592654) - 180.0) < 0.001)  # π = 180°
assert_true(abs(excel_degrees(6.283185307) - 360.0) < 0.001)  # 2π = 360°
```

</details>

#### RADIANS converts degrees to radians

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(abs(excel_radians(0.0) - 0.0) < 0.000001)
assert_true(abs(excel_radians(90.0) - 1.570796327) < 0.001)  # 90° = π/2
assert_true(abs(excel_radians(180.0) - 3.141592654) < 0.001)  # 180° = π
assert_true(abs(excel_radians(360.0) - 6.283185307) < 0.001)  # 360° = 2π
```

</details>

### Edge Cases

#### Empty array aggregate behavior

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(excel_sum([]), 0.0)
assert_equal(excel_product([]), 1.0)
assert_equal(excel_average([]), 0.0)  # Should handle gracefully
assert_equal(excel_min([]), 0.0)
assert_equal(excel_max([]), 0.0)
```

</details>

#### Single element arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(excel_sum([5.0]), 5.0)
assert_equal(excel_average([5.0]), 5.0)
assert_equal(excel_min([5.0]), 5.0)
assert_equal(excel_max([5.0]), 5.0)
assert_equal(excel_product([5.0]), 5.0)
```

</details>

#### Negative numbers in aggregates

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(excel_sum([-1.0, -2.0, -3.0]), -6.0)
assert_equal(excel_average([2.0, -2.0]), 0.0)
assert_equal(excel_min([-5.0, -10.0]), -10.0)
assert_equal(excel_max([-5.0, -10.0]), -5.0)
```

</details>

#### Mixed positive and negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(excel_sum([-5.0, 10.0, -3.0, 8.0]), 10.0)
assert_true(excel_average([2.0, -2.0, 4.0, -4.0]) > -0.001)
assert_true(excel_average([2.0, -2.0, 4.0, -4.0]) < 0.001)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/math_bridge_comprehensive_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Comprehensive Math Bridge Tests, Trigonometry, Logarithmic and Exponential, Statistical Aggregates, Rounding Functions, Angle Conversions, Edge Cases.
- Comprehensive Math Bridge Tests
- Trigonometry
- Logarithmic and Exponential
- Statistical Aggregates
- Rounding Functions
- Angle Conversions
- Edge Cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
