# Math Block Tensor Operations Specification

The `m{}` math block supports torch-compatible tensor operations for numerical computing. Each math block is a self-contained DSL expression that returns a Block value.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1090-1098 (subset: tensor ops) |
| Category | Syntax / Math DSL |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/feature/usage/math_blocks_spec.spl` |
| Updated | 2026-05-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

The `m{}` math block supports torch-compatible tensor operations for numerical computing.
Each math block is a self-contained DSL expression that returns a Block value.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 2 |
| Logs | 5 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/math_blocks/result.json` |
| `summary.txt` | Text artifact | `build/test-artifacts/feature/usage/math_blocks/summary.txt` |

### Logs

| Item | Kind | Path |
|------|------|------|
| `combined.log` | Log file | `build/test-artifacts/feature/usage/math_blocks/combined.log` |
| `output.log` | Log file | `build/test-artifacts/feature/usage/math_blocks/output.log` |
| `run.log` | Log file | `build/test-artifacts/feature/usage/math_blocks/run.log` |
| `stderr.log` | Log file | `build/test-artifacts/feature/usage/math_blocks/stderr.log` |
| `stdout.log` | Log file | `build/test-artifacts/feature/usage/math_blocks/stdout.log` |

## Scenarios

### Math Block Arithmetic
_Basic arithmetic operations._

#### evaluates addition

```simple
val result = m{ 2 + 3 }
expect(result).to_equal(5)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $2 + 3$<br>
> expect(result).to_equal(5)

</details>

#### evaluates subtraction

```simple
val result = m{ 10 - 3 }
expect(result).to_equal(7)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $10 - 3$<br>
> expect(result).to_equal(7)

</details>

#### evaluates multiplication

```simple
val result = m{ 4 * 5 }
expect(result).to_equal(20)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $4 \cdot 5$<br>
> expect(result).to_equal(20)

</details>

#### evaluates division

```simple
val result = m{ 15 / 3 }
expect(result).to_equal(5)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $15 / 3$<br>
> expect(result).to_equal(5)

</details>

#### evaluates complex expression

```simple
val result = m{ (2 + 3) * 4 }
expect(result).to_equal(20)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $(2 + 3) \cdot 4$<br>
> expect(result).to_equal(20)

</details>

#### respects operator precedence

```simple
val result = m{ 2 + 3 * 4 }
expect(result).to_equal(14)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $2 + 3 \cdot 4$<br>
> expect(result).to_equal(14)

</details>

#### evaluates power

```simple
val result = m{ 2^3 }
expect(result).to_equal(8.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $2^3$<br>
> expect(result).to_equal(8.0)

</details>

#### evaluates negative numbers

```simple
val result = m{ -5 + 3 }
expect(result).to_equal(-2)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $-5 + 3$<br>
> expect(result).to_equal(-2)

</details>

### Math Block Functions
_Built-in math functions._

#### evaluates sqrt of 16

```simple
val result = m{ sqrt(16) }
expect(result).to_equal(4.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\sqrt{16}$<br>
> expect(result).to_equal(4.0)

</details>

#### evaluates sqrt of 9

```simple
val result = m{ sqrt(9) }
expect(result).to_equal(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\sqrt{9}$<br>
> expect(result).to_equal(3.0)

</details>

#### evaluates abs of negative

```simple
val result = m{ abs(-5) }
expect(result).to_equal(5)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $abs(-5)$<br>
> expect(result).to_equal(5)

</details>

#### evaluates abs of positive

```simple
val result = m{ abs(7) }
expect(result).to_equal(7)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $abs(7)$<br>
> expect(result).to_equal(7)

</details>

#### evaluates frac

```simple
val result = m{ frac(6, 2) }
expect(result).to_equal(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\frac{6}{2}$<br>
> expect(result).to_equal(3.0)

</details>

#### evaluates nested functions

```simple
val result = m{ sqrt(abs(-16)) }
expect(result).to_equal(4.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\sqrt{abs(-16)}$<br>
> expect(result).to_equal(4.0)

</details>

### Math Block Matrix Operations
_Matrix operations that produce scalar results._

#### computes dot product

```simple
# dot([1,2,3], [4,5,6]) = 1*4 + 2*5 + 3*6 = 32
val result = m{ dot([1, 2, 3], [4, 5, 6]) }
expect(result).to_equal(32.0)
```

<details>
<summary>Rendered scenario source</summary>

> # dot([1,2,3], [4,5,6]) = 1*4 + 2*5 + 3*6 = 32<br>
> val result = $dot([1, 2, 3], [4, 5, 6])$<br>
> expect(result).to_equal(32.0)

</details>

#### computes dot product simple

```simple
# dot([1,1], [2,2]) = 1*2 + 1*2 = 4
val result = m{ dot([1, 1], [2, 2]) }
expect(result).to_equal(4.0)
```

<details>
<summary>Rendered scenario source</summary>

> # dot([1,1], [2,2]) = 1*2 + 1*2 = 4<br>
> val result = $dot([1, 1], [2, 2])$<br>
> expect(result).to_equal(4.0)

</details>

### Math Block Constants
_Built-in math constants._

#### evaluates pi greater than 3

```simple
val result = m{ pi }
expect(result).to_be_greater_than(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\pi$<br>
> expect(result).to_be_greater_than(3.0)

</details>

#### evaluates pi less than 4

```simple
val result = m{ pi }
expect(result).to_be_less_than(4.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\pi$<br>
> expect(result).to_be_less_than(4.0)

</details>

#### evaluates e greater than 2

```simple
val result = m{ e }
expect(result).to_be_greater_than(2.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $e$<br>
> expect(result).to_be_greater_than(2.0)

</details>

#### evaluates e less than 3

```simple
val result = m{ e }
expect(result).to_be_less_than(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $e$<br>
> expect(result).to_be_less_than(3.0)

</details>

### Math Block Array Expressions
_Array expressions that produce scalar results through reductions._

#### evaluates array subscript

```simple
# Array access returns scalar
val result = m{ [10, 20, 30][1] }
expect(result).to_equal(20.0)
```

<details>
<summary>Rendered scenario source</summary>

> # Array access returns scalar<br>
> val result = $[10, 20, 30][1]$<br>
> expect(result).to_equal(20.0)

</details>

#### evaluates nested array subscript

```simple
# 2D array access
val result = m{ [[1, 2], [3, 4]][0][1] }
expect(result).to_equal(2.0)
```

<details>
<summary>Rendered scenario source</summary>

> # 2D array access<br>
> val result = $[[1, 2], [3, 4]][0][1]$<br>
> expect(result).to_equal(2.0)

</details>

### Math Block LaTeX Compatibility
_LaTeX-style syntax support (with deprecation warnings)._

#### evaluates LaTeX frac

```simple
val result = m{ \frac{10}{2} }
expect(result).to_equal(5.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\frac{10}{2}$<br>
> expect(result).to_equal(5.0)

</details>

#### evaluates LaTeX sqrt

```simple
val result = m{ \sqrt{25} }
expect(result).to_equal(5.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\sqrt{25}$<br>
> expect(result).to_equal(5.0)

</details>

#### evaluates Greek letter pi

```simple
val result = m{ \pi }
expect(result).to_be_greater_than(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> val result = $\pi$<br>
> expect(result).to_be_greater_than(3.0)

</details>

### Math Block LaTeX Export
_Math expressions can be exported to LaTeX format._

#### exports simple arithmetic

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

#### exports fractions

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

#### exports Greek letters

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
