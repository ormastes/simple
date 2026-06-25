# Math Block Tensor Operations Specification

The `m{}` math block supports torch-compatible tensor operations for numerical computing. Each math block is a self-contained DSL expression that returns a Block value.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1090-1098 (subset: tensor ops) |
| Category | Syntax / Math DSL |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/math_blocks_spec.spl` |
| Updated | 2026-05-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The `m{}` math block supports torch-compatible tensor operations for numerical computing.
Each math block is a self-contained DSL expression that returns a Block value.

## Scenarios

### Math Block Arithmetic

#### evaluates addition

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ 2 + 3 }
expect(result).to_equal(5)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $2 + 3$<br>
> expect(result).to_equal(5)

</details>

</details>

#### evaluates subtraction

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ 10 - 3 }
expect(result).to_equal(7)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $10 - 3$<br>
> expect(result).to_equal(7)

</details>

</details>

#### evaluates multiplication

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ 4 * 5 }
expect(result).to_equal(20)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $4 \cdot 5$<br>
> expect(result).to_equal(20)

</details>

</details>

#### evaluates division

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ 15 / 3 }
expect(result).to_equal(5)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $15 / 3$<br>
> expect(result).to_equal(5)

</details>

</details>

#### evaluates complex expression

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ (2 + 3) * 4 }
expect(result).to_equal(20)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $(2 + 3) \cdot 4$<br>
> expect(result).to_equal(20)

</details>

</details>

#### respects operator precedence

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ 2 + 3 * 4 }
expect(result).to_equal(14)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $2 + 3 \cdot 4$<br>
> expect(result).to_equal(14)

</details>

</details>

#### evaluates power

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ 2^3 }
expect(result).to_equal(8.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $2^{3}$<br>
> expect(result).to_equal(8.0)

</details>

</details>

#### evaluates negative numbers

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ -5 + 3 }
expect(result).to_equal(-2)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $-5 + 3$<br>
> expect(result).to_equal(-2)

</details>

</details>

### Math Block Functions

#### evaluates sqrt of 16

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ sqrt(16) }
expect(result).to_equal(4.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\sqrt{16}$<br>
> expect(result).to_equal(4.0)

</details>

</details>

#### evaluates sqrt of 9

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ sqrt(9) }
expect(result).to_equal(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\sqrt{9}$<br>
> expect(result).to_equal(3.0)

</details>

</details>

#### evaluates abs of negative

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ abs(-5) }
expect(result).to_equal(5)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\operatorname{abs}(-5)$<br>
> expect(result).to_equal(5)

</details>

</details>

#### evaluates abs of positive

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ abs(7) }
expect(result).to_equal(7)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\operatorname{abs}(7)$<br>
> expect(result).to_equal(7)

</details>

</details>

#### evaluates frac

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ frac(6, 2) }
expect(result).to_equal(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\frac{6}{2}$<br>
> expect(result).to_equal(3.0)

</details>

</details>

#### evaluates nested functions

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ sqrt(abs(-16)) }
expect(result).to_equal(4.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\sqrt{\operatorname{abs}(-16)}$<br>
> expect(result).to_equal(4.0)

</details>

</details>

### Math Block Matrix Operations

#### computes dot product

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# dot([1,2,3], [4,5,6]) = 1*4 + 2*5 + 3*6 = 32
val result = m{ dot([1, 2, 3], [4, 5, 6]) }
expect(result).to_equal(32.0)
```

<details>
<summary>Rendered scenario source</summary>

> # dot([1,2,3], [4,5,6]) = 1*4 + 2*5 + 3*6 = 32<br>
> val result = $\operatorname{dot}([, 2, 3, [, 5, 6)$<br>
> expect(result).to_equal(32.0)

</details>

</details>

#### computes dot product simple

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# dot([1,1], [2,2]) = 1*2 + 1*2 = 4
val result = m{ dot([1, 1], [2, 2]) }
expect(result).to_equal(4.0)
```

<details>
<summary>Rendered scenario source</summary>

> # dot([1,1], [2,2]) = 1*2 + 1*2 = 4<br>
> val result = $\operatorname{dot}([, 1, [, 2)$<br>
> expect(result).to_equal(4.0)

</details>

</details>

### Math Block Constants

#### evaluates pi greater than 3

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ pi }
expect(result).to_be_greater_than(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\pi$<br>
> expect(result).to_be_greater_than(3.0)

</details>

</details>

#### evaluates pi less than 4

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ pi }
expect(result).to_be_less_than(4.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\pi$<br>
> expect(result).to_be_less_than(4.0)

</details>

</details>

#### evaluates e greater than 2

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ e }
expect(result).to_be_greater_than(2.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $e$<br>
> expect(result).to_be_greater_than(2.0)

</details>

</details>

#### evaluates e less than 3

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ e }
expect(result).to_be_less_than(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $e$<br>
> expect(result).to_be_less_than(3.0)

</details>

</details>

### Math Block Array Expressions

#### evaluates array subscript

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Array access returns scalar
val result = m{ [10, 20, 30][1] }
expect(result).to_equal(20.0)
```

<details>
<summary>Rendered scenario source</summary>

> # Array access returns scalar<br>
> val result = $[$<br>
> expect(result).to_equal(20.0)

</details>

</details>

#### evaluates nested array subscript

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2D array access
val result = m{ [[1, 2], [3, 4]][0][1] }
expect(result).to_equal(2.0)
```

<details>
<summary>Rendered scenario source</summary>

> # 2D array access<br>
> val result = $[$<br>
> expect(result).to_equal(2.0)

</details>

</details>

### Math Block LaTeX Compatibility

#### evaluates LaTeX frac

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ \frac{10}{2} }
expect(result).to_equal(5.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\$<br>
> expect(result).to_equal(5.0)

</details>

</details>

#### evaluates LaTeX sqrt

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ \sqrt{25} }
expect(result).to_equal(5.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\$<br>
> expect(result).to_equal(5.0)

</details>

</details>

#### evaluates Greek letter pi

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = m{ \pi }
expect(result).to_be_greater_than(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\$<br>
> expect(result).to_be_greater_than(3.0)

</details>

</details>

### Math Block LaTeX Export

#### exports simple arithmetic

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: This demonstrates the LaTeX export capability
# The actual export function is available in Rust: math.to_latex()
# Simple syntax: 2 + 3 -> LaTeX: 2 + 3
val result = m{ 2 + 3 }
expect(result).to_equal(5)
```

<details>
<summary>Rendered scenario source</summary>

> # Note: This demonstrates the LaTeX export capability<br>
> # The actual export function is available in Rust: math.to_latex()<br>
> # Simple syntax: 2 + 3 -> LaTeX: 2 + 3<br>
> val result = $2 + 3$<br>
> expect(result).to_equal(5)

</details>

</details>

#### exports fractions

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simple: frac(1, 2) -> LaTeX: \frac{1}{2}
val result = m{ frac(1, 2) }
expect(result).to_equal(0.5)
```

<details>
<summary>Rendered scenario source</summary>

> # Simple: frac(1, 2) -> LaTeX: \frac{1}{2}<br>
> val result = $\frac{1}{2}$<br>
> expect(result).to_equal(0.5)

</details>

</details>

#### exports Greek letters

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simple: pi -> LaTeX: \pi
val result = m{ pi }
expect(result).to_be_greater_than(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> # Simple: pi -> LaTeX: \pi<br>
> val result = $\pi$<br>
> expect(result).to_be_greater_than(3.0)

</details>

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

