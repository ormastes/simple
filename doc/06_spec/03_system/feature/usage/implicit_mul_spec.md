# Implicit Multiplication Specification

> Implicit multiplication in m{} math blocks:

<!-- sdn-diagram:id=implicit_mul_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=implicit_mul_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

implicit_mul_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=implicit_mul_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Implicit Multiplication Specification

Implicit multiplication in m{} math blocks:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2240-2245 |
| Category | Syntax |
| Status | Implemented |
| Source | `test/03_system/feature/usage/implicit_mul_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Implicit multiplication in m{} math blocks:
- `2x` → `2 * x`
- `2(x+1)` → `2 * (x+1)`
- `(a)(b)` → `(a) * (b)`
- `(x+1)y` → `(x+1) * y`

## Scenarios

### Implicit Multiplication in m{}

#### number followed by identifier

#### treats 2x as 2*x

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val x = 5
val result = m{ 2x }
expect result == 10
```

<details>
<summary>Rendered scenario source</summary>

> <br>
> val x = 5<br>
> val result = $2$<br>
> expect result == 10

</details>

</details>

#### treats 3y as 3*y

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val y = 7
val result = m{ 3y }
expect result == 21
```

<details>
<summary>Rendered scenario source</summary>

> <br>
> val y = 7<br>
> val result = $3$<br>
> expect result == 21

</details>

</details>

#### works with floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val x = 4.0
val result = m{ 2.5x }
expect result == 10.0
```

<details>
<summary>Rendered scenario source</summary>

> <br>
> val x = 4.0<br>
> val result = $2.5$<br>
> expect result == 10.0

</details>

</details>

#### number followed by parentheses

#### treats 2(x+1) as 2*(x+1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val x = 3
val result = m{ 2(x + 1) }
expect result == 8
```

<details>
<summary>Rendered scenario source</summary>

> <br>
> val x = 3<br>
> val result = $2$<br>
> expect result == 8

</details>

</details>

#### works in complex expressions

1. expect result == 27 0  # 3 *


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val x = 2
val result = m{ 3(x + 1)^2 }
expect result == 27.0  # 3 * (3)^2 = 3 * 9
```

<details>
<summary>Rendered scenario source</summary>

> <br>
> val x = 2<br>
> val result = $3$<br>
> expect result == 27.0  # 3 * (3)^2 = 3 * 9

</details>

</details>

#### parentheses followed by parentheses

#### treats (a)(b) as (a)*(b)

1. expect result == 6  #


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val a = 2
val b = 3
val result = m{ (a + 1)(b - 1) }
expect result == 6  # (3) * (2)
```

<details>
<summary>Rendered scenario source</summary>

> <br>
> val a = 2<br>
> val b = 3<br>
> val result = $(a + 1)$<br>
> expect result == 6  # (3) * (2)

</details>

</details>

#### chains multiple groups

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val a = 2
val result = m{ (a)(a)(a) }
expect result == 8  # 2 * 2 * 2
```

<details>
<summary>Rendered scenario source</summary>

> <br>
> val a = 2<br>
> val result = $(a)$<br>
> expect result == 8  # 2 * 2 * 2

</details>

</details>

#### parentheses followed by identifier

#### treats (x+1)y as (x+1)*y

1. expect result == 12  #


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val x = 2
val y = 4
val result = m{ (x + 1)y }
expect result == 12  # (3) * 4
```

<details>
<summary>Rendered scenario source</summary>

> <br>
> val x = 2<br>
> val y = 4<br>
> val result = $(x + 1)$<br>
> expect result == 12  # (3) * 4

</details>

</details>

#### complex expressions

#### computes quadratic with implicit mul

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val x = 3
val result = m{ 2x^2 + 3x + 1 }
expect result == 28.0  # 2*9 + 3*3 + 1
```

<details>
<summary>Rendered scenario source</summary>

> <br>
> val x = 3<br>
> val result = $2$<br>
> expect result == 28.0  # 2*9 + 3*3 + 1

</details>

</details>

#### computes polynomial

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val x = 2
val result = m{ x^3 + 2x^2 + 3x + 4 }
expect result == 26.0  # 8 + 8 + 6 + 4
```

<details>
<summary>Rendered scenario source</summary>

> <br>
> val x = 2<br>
> val result = $x^{3} + 2$<br>
> expect result == 26.0  # 8 + 8 + 6 + 4

</details>

</details>

#### mixes explicit and implicit mul

1. expect result == 18  #


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val x = 3
val result = m{ 2x * 3 }
expect result == 18  # (2*3) * 3
```

<details>
<summary>Rendered scenario source</summary>

> <br>
> val x = 3<br>
> val result = $2$<br>
> expect result == 18  # (2*3) * 3

</details>

</details>

#### handles scientific notation style

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val pi = 3.14159
val r = 2
val area = m{ pi r^2 }
expect(area).to_be_greater_than(12.56)
expect(area).to_be_less_than(12.57)
```

<details>
<summary>Rendered scenario source</summary>

> <br>
> val pi = 3.14159<br>
> val r = 2<br>
> val area = $\pi$<br>
> expect(area).to_be_greater_than(12.56)<br>
> expect(area).to_be_less_than(12.57)

</details>

</details>

#### matrix expressions

<details>
<summary>Advanced: multiplies coefficient and matrix</summary>

#### multiplies coefficient and matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val A = [[1, 2], [3, 4]]
val result = m{ 2A }
expect result == [[2, 4], [6, 8]]
```

<details>
<summary>Rendered scenario source</summary>

> <br>
> val A = [[1, 2], [3, 4]]<br>
> val result = $2$<br>
> expect result == [[2, 4], [6, 8]]

</details>

</details>


</details>

#### works in linear algebra

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val A = [[1, 0], [0, 1]]
val x = [1, 2]
val b = [3, 4]
# 2Ax + b
val result = m{ 2(A @ x) + b }
expect result == [5, 8]
```

<details>
<summary>Rendered scenario source</summary>

> <br>
> val A = [[1, 0], [0, 1]]<br>
> val x = [1, 2]<br>
> val b = [3, 4]<br>
> # 2Ax + b<br>
> val result = $2$<br>
> expect result == [5, 8]

</details>

</details>

#### precedence

#### implicit mul has same precedence as explicit

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val x = 2
val y = 3
# 2x + 3y should be (2*x) + (3*y)
val result = m{ 2x + 3y }
expect result == 13  # 4 + 9
```

<details>
<summary>Rendered scenario source</summary>

> <br>
> val x = 2<br>
> val y = 3<br>
> # 2x + 3y should be (2*x) + (3*y)<br>
> val result = $2$<br>
> expect result == 13  # 4 + 9

</details>

</details>

#### power binds tighter

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val x = 2
# 2x^3 should be 2*(x^3) not (2*x)^3
val result = m{ 2x^3 }
expect result == 16.0  # 2 * 8
```

<details>
<summary>Rendered scenario source</summary>

> <br>
> val x = 2<br>
> # 2x^3 should be 2*(x^3) not (2*x)^3<br>
> val result = $2$<br>
> expect result == 16.0  # 2 * 8

</details>

</details>

#### outside m{} blocks

#### does NOT allow implicit mul outside m{}

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This should not compile or should require explicit *
val x = 5
# val result = 2x  # ERROR: would not work
val result = 2 * x  # Must use explicit *
expect result == 10
```

</details>

### Implicit Multiplication Edge Cases

#### function calls are NOT implicit mul

#### preserves function call syntax

1. fn double


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x: i64) -> i64:
    x * 2

val x = 5
# x(5) would be invalid, not x * 5
# In m{}, we need to be careful
val result = double(x)
expect result == 10
```

</details>

#### negative numbers

#### handles negative coefficient

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3
val result = m{ -2x }
expect result == -6
```

<details>
<summary>Rendered scenario source</summary>

> val x = 3<br>
> val result = $-2$<br>
> expect result == -6

</details>

</details>

#### handles subtraction vs negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val x = 3
val y = 2
# -x y should be (-x) * y
val result = m{ -x y }
expect result == -6
```

<details>
<summary>Rendered scenario source</summary>

> <br>
> val x = 3<br>
> val y = 2<br>
> # -x y should be (-x) * y<br>
> val result = $-x$<br>
> expect result == -6

</details>

</details>

#### whitespace

#### works without spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val x = 5
val result = m{ 2x+3 }
expect result == 13
```

<details>
<summary>Rendered scenario source</summary>

> <br>
> val x = 5<br>
> val result = $2$<br>
> expect result == 13

</details>

</details>

#### works with spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val x = 5
val result = m{ 2 x + 3 }
expect result == 13
```

<details>
<summary>Rendered scenario source</summary>

> <br>
> val x = 5<br>
> val result = $2$<br>
> expect result == 13

</details>

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
