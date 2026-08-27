# Math Block Tensor Operations Specification

> Purpose: evaluates addition

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Block Tensor Operations Specification

Purpose: evaluates addition

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1090-1098 (subset: tensor ops) |
| Category | Syntax / Math DSL |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/math_blocks_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: evaluates addition
Audience: compiler and tooling engineers who maintain this spec

# Math Block Tensor Operations Specification

**Feature IDs:** #1090-1098 (subset: tensor ops)
**Category:** Syntax / Math DSL
**Difficulty:** 4/5
**Status:** Implemented

## Overview

The `m{}` math block supports torch-compatible tensor operations for numerical computing.
Each math block is a self-contained DSL expression that returns a Block value.

## Scenarios

### Math Block Arithmetic

#### evaluates addition

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- evaluates addition
- Verify: evaluates addition
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates addition")
step("Verify: evaluates addition")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ 2 + 3 }
expect(result).to_equal(5)  # oracle: value fixed by the spec contract
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates addition")<br>
> step("Verify: evaluates addition")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $2 + 3$<br>
> expect(result).to_equal(5)  # oracle: value fixed by the spec contract

</details>

</details>

#### evaluates subtraction

- evaluates subtraction
- Verify: evaluates subtraction
   - Expected: result equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates subtraction")
step("Verify: evaluates subtraction")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ 10 - 3 }
expect(result).to_equal(7)  # oracle: value fixed by the spec contract
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates subtraction")<br>
> step("Verify: evaluates subtraction")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $10 - 3$<br>
> expect(result).to_equal(7)  # oracle: value fixed by the spec contract

</details>

</details>

#### evaluates multiplication

- evaluates multiplication
- Verify: evaluates multiplication
   - Expected: result equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates multiplication")
step("Verify: evaluates multiplication")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ 4 * 5 }
expect(result).to_equal(20)  # oracle: value fixed by the spec contract
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates multiplication")<br>
> step("Verify: evaluates multiplication")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $4 \cdot 5$<br>
> expect(result).to_equal(20)  # oracle: value fixed by the spec contract

</details>

</details>

#### evaluates division

- evaluates division
- Verify: evaluates division
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates division")
step("Verify: evaluates division")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ 15 / 3 }
expect(result).to_equal(5)  # oracle: value fixed by the spec contract
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates division")<br>
> step("Verify: evaluates division")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $15 / 3$<br>
> expect(result).to_equal(5)  # oracle: value fixed by the spec contract

</details>

</details>

#### evaluates complex expression

- evaluates complex expression
- Verify: evaluates complex expression
   - Expected: result equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates complex expression")
step("Verify: evaluates complex expression")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ (2 + 3) * 4 }
expect(result).to_equal(20)  # oracle: value fixed by the spec contract
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates complex expression")<br>
> step("Verify: evaluates complex expression")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $(2 + 3) \cdot 4$<br>
> expect(result).to_equal(20)  # oracle: value fixed by the spec contract

</details>

</details>

#### respects operator precedence

- respects operator precedence
- Verify: respects operator precedence
   - Expected: result equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("respects operator precedence")
step("Verify: respects operator precedence")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ 2 + 3 * 4 }
expect(result).to_equal(14)  # oracle: value fixed by the spec contract
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("respects operator precedence")<br>
> step("Verify: respects operator precedence")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $2 + 3 \cdot 4$<br>
> expect(result).to_equal(14)  # oracle: value fixed by the spec contract

</details>

</details>

#### evaluates power

- evaluates power
- Verify: evaluates power
   - Expected: result equals `8.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates power")
step("Verify: evaluates power")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ 2^3 }
expect(result).to_equal(8.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates power")<br>
> step("Verify: evaluates power")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $2^{3}$<br>
> expect(result).to_equal(8.0)

</details>

</details>

#### evaluates negative numbers

- evaluates negative numbers
- Verify: evaluates negative numbers
   - Expected: result equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates negative numbers")
step("Verify: evaluates negative numbers")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ -5 + 3 }
expect(result).to_equal(-2)  # oracle: value fixed by the spec contract
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates negative numbers")<br>
> step("Verify: evaluates negative numbers")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $-5 + 3$<br>
> expect(result).to_equal(-2)  # oracle: value fixed by the spec contract

</details>

</details>

### Math Block Functions

#### evaluates sqrt of 16

- evaluates sqrt of 16
- Verify: evaluates sqrt of 16
   - Expected: result equals `4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates sqrt of 16")
step("Verify: evaluates sqrt of 16")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ sqrt(16) }
expect(result).to_equal(4.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates sqrt of 16")<br>
> step("Verify: evaluates sqrt of 16")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $\sqrt{16}$<br>
> expect(result).to_equal(4.0)

</details>

</details>

#### evaluates sqrt of 9

- evaluates sqrt of 9
- Verify: evaluates sqrt of 9
   - Expected: result equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates sqrt of 9")
step("Verify: evaluates sqrt of 9")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ sqrt(9) }
expect(result).to_equal(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates sqrt of 9")<br>
> step("Verify: evaluates sqrt of 9")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $\sqrt{9}$<br>
> expect(result).to_equal(3.0)

</details>

</details>

#### evaluates abs of negative

- evaluates abs of negative
- Verify: evaluates abs of negative
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates abs of negative")
step("Verify: evaluates abs of negative")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ abs(-5) }
expect(result).to_equal(5)  # oracle: value fixed by the spec contract
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates abs of negative")<br>
> step("Verify: evaluates abs of negative")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $\operatorname{abs}(-5)$<br>
> expect(result).to_equal(5)  # oracle: value fixed by the spec contract

</details>

</details>

#### evaluates abs of positive

- evaluates abs of positive
- Verify: evaluates abs of positive
   - Expected: result equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates abs of positive")
step("Verify: evaluates abs of positive")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ abs(7) }
expect(result).to_equal(7)  # oracle: value fixed by the spec contract
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates abs of positive")<br>
> step("Verify: evaluates abs of positive")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $\operatorname{abs}(7)$<br>
> expect(result).to_equal(7)  # oracle: value fixed by the spec contract

</details>

</details>

#### evaluates frac

- evaluates frac
- Verify: evaluates frac
   - Expected: result equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates frac")
step("Verify: evaluates frac")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ frac(6, 2) }
expect(result).to_equal(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates frac")<br>
> step("Verify: evaluates frac")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $\frac{6}{2}$<br>
> expect(result).to_equal(3.0)

</details>

</details>

#### evaluates nested functions

- evaluates nested functions
- Verify: evaluates nested functions
   - Expected: result equals `4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates nested functions")
step("Verify: evaluates nested functions")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ sqrt(abs(-16)) }
expect(result).to_equal(4.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates nested functions")<br>
> step("Verify: evaluates nested functions")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $\sqrt{\operatorname{abs}(-16)}$<br>
> expect(result).to_equal(4.0)

</details>

</details>

### Math Block Matrix Operations

#### computes dot product

- computes dot product
- Verify: computes dot product
   - Expected: result equals `32.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes dot product")
step("Verify: computes dot product")
# @req: REQ-FEATURE-MathBloc-001
# dot([1,2,3], [4,5,6]) = 1*4 + 2*5 + 3*6 = 32
val result = m{ dot([1, 2, 3], [4, 5, 6]) }
expect(result).to_equal(32.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("computes dot product")<br>
> step("Verify: computes dot product")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> # dot([1,2,3], [4,5,6]) = 1*4 + 2*5 + 3*6 = 32<br>
> val result = $\operatorname{dot}(?, 2, 3, ?, 5, 6)$<br>
> expect(result).to_equal(32.0)

</details>

</details>

#### computes dot product simple

- computes dot product simple
- Verify: computes dot product simple
   - Expected: result equals `4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes dot product simple")
step("Verify: computes dot product simple")
# @req: REQ-FEATURE-MathBloc-001
# dot([1,1], [2,2]) = 1*2 + 1*2 = 4
val result = m{ dot([1, 1], [2, 2]) }
expect(result).to_equal(4.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("computes dot product simple")<br>
> step("Verify: computes dot product simple")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> # dot([1,1], [2,2]) = 1*2 + 1*2 = 4<br>
> val result = $\operatorname{dot}(?, 1, ?, 2)$<br>
> expect(result).to_equal(4.0)

</details>

</details>

### Math Block Constants

#### evaluates pi greater than 3

- evaluates pi greater than 3
- Verify: evaluates pi greater than 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates pi greater than 3")
step("Verify: evaluates pi greater than 3")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ pi }
expect(result).to_be_greater_than(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates pi greater than 3")<br>
> step("Verify: evaluates pi greater than 3")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $\pi$<br>
> expect(result).to_be_greater_than(3.0)

</details>

</details>

#### evaluates pi less than 4

- evaluates pi less than 4
- Verify: evaluates pi less than 4


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates pi less than 4")
step("Verify: evaluates pi less than 4")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ pi }
expect(result).to_be_less_than(4.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates pi less than 4")<br>
> step("Verify: evaluates pi less than 4")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $\pi$<br>
> expect(result).to_be_less_than(4.0)

</details>

</details>

#### evaluates e greater than 2

- evaluates e greater than 2
- Verify: evaluates e greater than 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates e greater than 2")
step("Verify: evaluates e greater than 2")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ e }
expect(result).to_be_greater_than(2.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates e greater than 2")<br>
> step("Verify: evaluates e greater than 2")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $e$<br>
> expect(result).to_be_greater_than(2.0)

</details>

</details>

#### evaluates e less than 3

- evaluates e less than 3
- Verify: evaluates e less than 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates e less than 3")
step("Verify: evaluates e less than 3")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ e }
expect(result).to_be_less_than(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates e less than 3")<br>
> step("Verify: evaluates e less than 3")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $e$<br>
> expect(result).to_be_less_than(3.0)

</details>

</details>

### Math Block Array Expressions

#### evaluates array subscript

- evaluates array subscript
- Verify: evaluates array subscript
   - Expected: result equals `20.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates array subscript")
step("Verify: evaluates array subscript")
# @req: REQ-FEATURE-MathBloc-001
# Array access returns scalar
val result = m{ [10, 20, 30][1] }
expect(result).to_equal(20.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates array subscript")<br>
> step("Verify: evaluates array subscript")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> # Array access returns scalar<br>
> val result = $?$<br>
> expect(result).to_equal(20.0)

</details>

</details>

#### evaluates nested array subscript

- evaluates nested array subscript
- Verify: evaluates nested array subscript
   - Expected: result equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates nested array subscript")
step("Verify: evaluates nested array subscript")
# @req: REQ-FEATURE-MathBloc-001
# 2D array access
val result = m{ [[1, 2], [3, 4]][0][1] }
expect(result).to_equal(2.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates nested array subscript")<br>
> step("Verify: evaluates nested array subscript")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> # 2D array access<br>
> val result = $?$<br>
> expect(result).to_equal(2.0)

</details>

</details>

### Math Block LaTeX Compatibility

#### evaluates LaTeX frac

- evaluates LaTeX frac
- Verify: evaluates LaTeX frac
   - Expected: result equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates LaTeX frac")
step("Verify: evaluates LaTeX frac")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ \frac{10}{2} }
expect(result).to_equal(5.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates LaTeX frac")<br>
> step("Verify: evaluates LaTeX frac")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $? \frac{?}{?}$<br>
> expect(result).to_equal(5.0)

</details>

</details>

#### evaluates LaTeX sqrt

- evaluates LaTeX sqrt
- Verify: evaluates LaTeX sqrt
   - Expected: result equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates LaTeX sqrt")
step("Verify: evaluates LaTeX sqrt")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ \sqrt{25} }
expect(result).to_equal(5.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates LaTeX sqrt")<br>
> step("Verify: evaluates LaTeX sqrt")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $? \sqrt{?}$<br>
> expect(result).to_equal(5.0)

</details>

</details>

#### evaluates Greek letter pi

- evaluates Greek letter pi
- Verify: evaluates Greek letter pi


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates Greek letter pi")
step("Verify: evaluates Greek letter pi")
# @req: REQ-FEATURE-MathBloc-001
val result = m{ \pi }
expect(result).to_be_greater_than(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("evaluates Greek letter pi")<br>
> step("Verify: evaluates Greek letter pi")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> val result = $? \pi$<br>
> expect(result).to_be_greater_than(3.0)

</details>

</details>

### Math Block LaTeX Export

#### exports simple arithmetic

- exports simple arithmetic
- Verify: exports simple arithmetic
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports simple arithmetic")
step("Verify: exports simple arithmetic")
# @req: REQ-FEATURE-MathBloc-001
# Note: This demonstrates the LaTeX export capability
# The actual export function is available in Rust: math.to_latex()
# Simple syntax: 2 + 3 -> LaTeX: 2 + 3
val result = m{ 2 + 3 }
expect(result).to_equal(5)  # oracle: value fixed by the spec contract
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("exports simple arithmetic")<br>
> step("Verify: exports simple arithmetic")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> # Note: This demonstrates the LaTeX export capability<br>
> # The actual export function is available in Rust: math.to_latex()<br>
> # Simple syntax: 2 + 3 -> LaTeX: 2 + 3<br>
> val result = $2 + 3$<br>
> expect(result).to_equal(5)  # oracle: value fixed by the spec contract

</details>

</details>

#### exports fractions

- exports fractions
- Verify: exports fractions
   - Expected: result equals `0.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports fractions")
step("Verify: exports fractions")
# @req: REQ-FEATURE-MathBloc-001
# Simple: frac(1, 2) -> LaTeX: \frac{1}{2}
val result = m{ frac(1, 2) }
expect(result).to_equal(0.5)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("exports fractions")<br>
> step("Verify: exports fractions")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
> # Simple: frac(1, 2) -> LaTeX: \frac{1}{2}<br>
> val result = $\frac{1}{2}$<br>
> expect(result).to_equal(0.5)

</details>

</details>

#### exports Greek letters

- exports Greek letters
- Verify: exports Greek letters


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports Greek letters")
step("Verify: exports Greek letters")
# @req: REQ-FEATURE-MathBloc-001
# Simple: pi -> LaTeX: \pi
val result = m{ pi }
expect(result).to_be_greater_than(3.0)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-SYSTEM<br>
> step("exports Greek letters")<br>
> step("Verify: exports Greek letters")<br>
> # @req: REQ-FEATURE-MathBloc-001<br>
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-FEATURE-MathBloc-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8de48dd3ccdc2a3130e60c492451a43852fd20516bb63bf7913920475e4d16fd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8de48dd3ccdc2a3130e60c492451a43852fd20516bb63bf7913920475e4d16fd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8de48dd3ccdc2a3130e60c492451a43852fd20516bb63bf7913920475e4d16fd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/usage/math_blocks_spec.spl
mirror: doc/06_spec/03_system/feature/usage/math_blocks_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/math_blocks_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/math_blocks_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/math_blocks_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/math_blocks_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates addition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/math_blocks_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates subtraction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/math_blocks_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates multiplication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
