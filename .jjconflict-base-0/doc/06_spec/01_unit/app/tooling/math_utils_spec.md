# Math Utils Specification

> 1. expect abs i64

<!-- sdn-diagram:id=math_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_utils_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Utils Specification

## Scenarios

### Math Utilities

### Absolute Value

#### returns positive for positive

1. expect abs i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect abs_i64(5) == 5
```

</details>

#### returns positive for negative

1. expect abs i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect abs_i64(-5) == 5
```

</details>

#### returns zero for zero

1. expect abs i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect abs_i64(0) == 0
```

</details>

### Min/Max

#### min returns smaller

1. expect min i64
2. expect min i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect min_i64(a=5, b=10) == 5
expect min_i64(a=-5, b=3) == -5
```

</details>

#### max returns larger

1. expect max i64
2. expect max i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect max_i64(a=5, b=10) == 10
expect max_i64(a=-5, b=3) == 3
```

</details>

### Clamp

#### clamps within range

1. expect clamp i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect clamp_i64(x=5, min_val=0, max_val=10) == 5
```

</details>

#### clamps below min

1. expect clamp i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect clamp_i64(x=-5, min_val=0, max_val=10) == 0
```

</details>

#### clamps above max

1. expect clamp i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect clamp_i64(x=15, min_val=0, max_val=10) == 10
```

</details>

### Sign

#### returns 1 for positive

1. expect sign i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect sign_i64(5) == 1
```

</details>

#### returns -1 for negative

1. expect sign i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect sign_i64(-5) == -1
```

</details>

#### returns 0 for zero

1. expect sign i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect sign_i64(0) == 0
```

</details>

### Power

#### calculates powers

1. expect pow i64
2. expect pow i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect pow_i64(base=2, exp=3) == 8
expect pow_i64(base=3, exp=2) == 9
```

</details>

#### handles zero exponent

1. expect pow i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect pow_i64(base=10, exp=0) == 1
```

</details>

#### handles zero base

1. expect pow i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect pow_i64(base=0, exp=5) == 0
```

</details>

#### handles negative base

1. expect pow i64
2. expect pow i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect pow_i64(base=-2, exp=3) == -8
expect pow_i64(base=-2, exp=4) == 16
```

</details>

### GCD and LCM

#### calculates gcd

1. expect gcd
2. expect gcd
3. expect gcd


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect gcd(a=12, b=8) == 4
expect gcd(a=21, b=14) == 7
expect gcd(a=17, b=19) == 1
```

</details>

#### gcd with same number

1. expect gcd


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect gcd(a=10, b=10) == 10
```

</details>

#### gcd with zero

1. expect gcd
2. expect gcd


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect gcd(a=0, b=5) == 5
expect gcd(a=5, b=0) == 5
```

</details>

#### calculates lcm

1. expect lcm
2. expect lcm


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect lcm(a=4, b=6) == 12
expect lcm(a=3, b=5) == 15
```

</details>

### Factorial and Binomial

#### calculates factorial

1. expect factorial
2. expect factorial
3. expect factorial


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect factorial(0) == 1
expect factorial(1) == 1
expect factorial(5) == 120
```

</details>

#### calculates binomial

1. expect binomial
2. expect binomial
3. expect binomial
4. expect binomial


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect binomial(n=5, k=2) == 10
expect binomial(n=4, k=2) == 6
expect binomial(n=5, k=0) == 1
expect binomial(n=5, k=5) == 1
```

</details>

### Even/Odd

#### detects even

1. expect is even
2. expect is even
3. expect is even
4. expect not is even


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_even(0)
expect is_even(2)
expect is_even(-4)
expect not is_even(1)
```

</details>

#### detects odd

1. expect is odd
2. expect is odd
3. expect not is odd


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_odd(1)
expect is_odd(3)
expect not is_odd(0)
```

</details>

### Divisibility

#### checks divisibility

1. expect is divisible by
2. expect is divisible by
3. expect not is divisible by


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_divisible_by(x=10, d=2)
expect is_divisible_by(x=15, d=5)
expect not is_divisible_by(x=7, d=3)
```

</details>

### Range

#### checks in range

1. expect in range i64
2. expect not in range i64
3. expect not in range i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect in_range_i64(x=5, min_val=0, max_val=10)
expect not in_range_i64(x=-1, min_val=0, max_val=10)
expect not in_range_i64(x=11, min_val=0, max_val=10)
```

</details>

### Statistics

#### calculates sum

1. expect sum i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect sum_i64([1, 2, 3, 4, 5]) == 15
```

</details>

#### sum of empty is 0

1. expect sum i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_list: [i64] = []
expect sum_i64(empty_list) == 0
```

</details>

#### calculates product

1. expect product i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect product_i64([2, 3, 4]) == 24
```

</details>

#### product of empty is 1

1. expect product i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_list: [i64] = []
expect product_i64(empty_list) == 1
```

</details>

#### calculates average

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = average_i64([1, 2, 3, 4, 5])
expect result == 3
```

</details>

#### average of empty is nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_list: [i64] = []
val result = average_i64(empty_list)
expect result == nil
```

</details>

#### calculates median odd

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = median_i64([1, 2, 3, 4, 5])
expect result == 3
```

</details>

#### calculates median even

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = median_i64([1, 2, 3, 4])
expect result == 2
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/math_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Math Utilities
- Absolute Value
- Min/Max
- Clamp
- Sign
- Power
- GCD and LCM
- Factorial and Binomial
- Even/Odd
- Divisibility
- Range
- Statistics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
