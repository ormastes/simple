# Math Specification

> <details>

<!-- sdn-diagram:id=math_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Specification

## Scenarios

### Math operations

#### Basic operations

#### abs returns absolute value of negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(abs_val(-5)).to_equal(5)
```

</details>

#### abs of positive is unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(abs_val(5)).to_equal(5)
```

</details>

#### abs of zero is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(abs_val(0)).to_equal(0)
```

</details>

#### sign returns -1 for negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sign_val(-5)).to_equal(-1)
```

</details>

#### sign returns 1 for positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sign_val(5)).to_equal(1)
```

</details>

#### sign returns 0 for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sign_val(0)).to_equal(0)
```

</details>

#### Min/Max functions

#### min returns smaller value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(min_val(3, 5)).to_equal(3)
```

</details>

#### min with equal values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(min_val(4, 4)).to_equal(4)
```

</details>

#### min with negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(min_val(-3, 5)).to_equal(-3)
```

</details>

#### max returns larger value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(max_val(3, 5)).to_equal(5)
```

</details>

#### max with equal values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(max_val(4, 4)).to_equal(4)
```

</details>

#### max with negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(max_val(-3, 5)).to_equal(5)
```

</details>

#### Clamping

#### clamp within range returns value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp_val(5, 0, 10)).to_equal(5)
```

</details>

#### clamp below range returns min

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp_val(-5, 0, 10)).to_equal(0)
```

</details>

#### clamp above range returns max

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp_val(15, 0, 10)).to_equal(10)
```

</details>

#### clamp at boundaries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp_val(0, 0, 10)).to_equal(0)
expect(clamp_val(10, 0, 10)).to_equal(10)
```

</details>

#### Integer math

#### factorial computes 5!

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(factorial(5)).to_equal(120)
```

</details>

#### factorial of 0 is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(factorial(0)).to_equal(1)
```

</details>

#### factorial of 1 is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(factorial(1)).to_equal(1)
```

</details>

#### factorial of 10

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(factorial(10)).to_equal(3628800)
```

</details>

#### gcd computes greatest common divisor

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gcd(12, 8)).to_equal(4)
```

</details>

#### gcd of coprime numbers is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gcd(7, 13)).to_equal(1)
```

</details>

#### gcd with zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gcd(5, 0)).to_equal(5)
expect(gcd(0, 5)).to_equal(5)
```

</details>

#### lcm computes least common multiple

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lcm(4, 6)).to_equal(12)
```

</details>

#### lcm of coprime numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lcm(3, 5)).to_equal(15)
```

</details>

#### lcm with zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lcm(0, 5)).to_equal(0)
```

</details>

#### Arithmetic properties

#### addition is commutative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(3 + 5).to_equal(5 + 3)
```

</details>

#### multiplication is commutative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(3 * 5).to_equal(5 * 3)
```

</details>

#### multiplication distributes over addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(3 * (4 + 5)).to_equal(3 * 4 + 3 * 5)
```

</details>

#### integer division truncates toward zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(7 / 2).to_equal(3)
expect(-7 / 2).to_equal(-3)
```

</details>

#### modulo gives remainder

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(7 % 3).to_equal(1)
expect(10 % 5).to_equal(0)
```

</details>

#### Power via repeated multiplication

#### computes x^0 = 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = 5
expect(1).to_equal(1)
```

</details>

#### computes 2^10 = 1024

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = 1
for _ in 0..10:
    result = result * 2
expect(result).to_equal(1024)
```

</details>

#### computes 3^5 = 243

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = 1
for _ in 0..5:
    result = result * 3
expect(result).to_equal(243)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/core/math_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Math operations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
