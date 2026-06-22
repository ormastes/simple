# Numeric Robustness Fuzz Specification

> 1. lcg seed

<!-- sdn-diagram:id=numeric_robustness_fuzz_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=numeric_robustness_fuzz_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

numeric_robustness_fuzz_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=numeric_robustness_fuzz_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Numeric Robustness Fuzz Specification

## Scenarios

### fuzz: numeric robustness

#### multiplication by zero always yields zero

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(20001)
var failures = 0
for i in 0..200:
    val n = lcg_range(-100000, 100000)
    if n * 0 != 0:
        failures = failures + 1
    if 0 * n != 0:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### multiplication by one is identity

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(20002)
var failures = 0
for i in 0..200:
    val n = lcg_range(-100000, 100000)
    if n * 1 != n:
        failures = failures + 1
    if 1 * n != n:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### multiplication by negative one negates

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(20003)
var failures = 0
for i in 0..200:
    val n = lcg_range(-100000, 100000)
    if n * -1 != -n:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### comparison consistency: a < b implies not b < a

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(20004)
var failures = 0
for i in 0..200:
    val a = lcg_range(-10000, 10000)
    val b = lcg_range(-10000, 10000)
    if a < b:
        if b < a:
            failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### comparison trichotomy: exactly one of <, ==, > holds

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(20005)
var failures = 0
for i in 0..200:
    val a = lcg_range(-10000, 10000)
    val b = lcg_range(-10000, 10000)
    var count = 0
    if a < b: count = count + 1
    if a == b: count = count + 1
    if a > b: count = count + 1
    if count != 1:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### modulo result has same sign behavior

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(20006)
var failures = 0
for i in 0..200:
    val divisor = lcg_range(1, 1000)
    val n = lcg_range(-10000, 10000)
    val remainder = n % divisor
    # remainder magnitude should be less than divisor
    if abs_val(remainder) >= divisor:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### division and modulo are consistent: n == (n / d) * d + (n % d)

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(20007)
var failures = 0
for i in 0..200:
    val d = lcg_range(1, 1000)
    val n = lcg_range(-10000, 10000)
    val quotient = n / d
    val remainder = n % d
    val reconstructed = quotient * d + remainder
    if reconstructed != n:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### subtraction is inverse of addition

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(20008)
var failures = 0
for i in 0..200:
    val a = lcg_range(-50000, 50000)
    val b = lcg_range(-50000, 50000)
    val sum = a + b
    val diff = sum - b
    if diff != a:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### addition is associative for random triples

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(20009)
var failures = 0
for i in 0..100:
    val a = lcg_range(-10000, 10000)
    val b = lcg_range(-10000, 10000)
    val c = lcg_range(-10000, 10000)
    val left = (a + b) + c
    val right = a + (b + c)
    if left != right:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### distributive law holds: a * (b + c) == a * b + a * c

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(20010)
var failures = 0
for i in 0..100:
    val a = lcg_range(-100, 100)
    val b = lcg_range(-100, 100)
    val c = lcg_range(-100, 100)
    val left = a * (b + c)
    val right = a * b + a * c
    if left != right:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### absolute value is always non-negative

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(20011)
var failures = 0
for i in 0..200:
    val n = lcg_range(-100000, 100000)
    val a = abs_val(n)
    if a < 0:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

#### large number addition does not silently lose precision

1. lcg seed
   - Expected: failures equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(20012)
var failures = 0
val big = 1000000000
for i in 0..100:
    val offset = lcg_range(0, 1000000)
    val n = big + offset
    val back = n - big
    if back != offset:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/language/fuzz/numeric_robustness_fuzz_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- fuzz: numeric robustness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
