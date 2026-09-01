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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The `m{}` math block supports torch-compatible tensor operations for numerical computing.
Each math block is a self-contained DSL expression that returns a Block value.

## Scenarios

### Math Block Arithmetic

#### evaluates addition

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- evaluates addition
- evaluates addition
   - Expected: result equals `5`


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

- evaluates subtraction
- evaluates subtraction
   - Expected: result equals `7`


<details>
<summary>Executable SSpec</summary>


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

- evaluates multiplication
- evaluates multiplication
   - Expected: result equals `20`


<details>
<summary>Executable SSpec</summary>


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

- evaluates division
- evaluates division
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>


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

- evaluates complex expression
- evaluates complex expression
   - Expected: result equals `20`


<details>
<summary>Executable SSpec</summary>


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

- respects operator precedence
- respects operator precedence
   - Expected: result equals `14`


<details>
<summary>Executable SSpec</summary>


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

- evaluates power
- evaluates power
   - Expected: result equals `8.0`


<details>
<summary>Executable SSpec</summary>


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

- evaluates negative numbers
- evaluates negative numbers
   - Expected: result equals `-2`


<details>
<summary>Executable SSpec</summary>


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

- evaluates sqrt of 16
- evaluates sqrt of 16
   - Expected: result equals `4.0`


<details>
<summary>Executable SSpec</summary>


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

- evaluates sqrt of 9
- evaluates sqrt of 9
   - Expected: result equals `3.0`


<details>
<summary>Executable SSpec</summary>


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

- evaluates abs of negative
- evaluates abs of negative
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>


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

- evaluates abs of positive
- evaluates abs of positive
   - Expected: result equals `7`


<details>
<summary>Executable SSpec</summary>


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

- evaluates frac
- evaluates frac
   - Expected: result equals `3.0`


<details>
<summary>Executable SSpec</summary>


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

- evaluates nested functions
- evaluates nested functions
   - Expected: result equals `4.0`


<details>
<summary>Executable SSpec</summary>


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

- computes dot product
- computes dot product
   - Expected: result equals `32.0`


<details>
<summary>Executable SSpec</summary>


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

- computes dot product simple
- computes dot product simple
   - Expected: result equals `4.0`


<details>
<summary>Executable SSpec</summary>


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

- evaluates pi greater than 3
- evaluates pi greater than 3


<details>
<summary>Executable SSpec</summary>


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

- evaluates pi less than 4
- evaluates pi less than 4


<details>
<summary>Executable SSpec</summary>


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

- evaluates e greater than 2
- evaluates e greater than 2


<details>
<summary>Executable SSpec</summary>


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

- evaluates e less than 3
- evaluates e less than 3


<details>
<summary>Executable SSpec</summary>


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

- evaluates array subscript
- evaluates array subscript
   - Expected: result equals `20.0`


<details>
<summary>Executable SSpec</summary>


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

- evaluates nested array subscript
- evaluates nested array subscript
   - Expected: result equals `2.0`


<details>
<summary>Executable SSpec</summary>


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

- evaluates LaTeX frac
- evaluates LaTeX frac
   - Expected: result equals `5.0`


<details>
<summary>Executable SSpec</summary>


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

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates LaTeX frac")<br>
> step("evaluates LaTeX frac")<br>
> val result = $? \frac{?}{?}$<br>
> expect(result).to_equal(5.0)

</details>

</details>

#### evaluates LaTeX sqrt

- evaluates LaTeX sqrt
- evaluates LaTeX sqrt
   - Expected: result equals `5.0`


<details>
<summary>Executable SSpec</summary>


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

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates LaTeX sqrt")<br>
> step("evaluates LaTeX sqrt")<br>
> val result = $? \sqrt{?}$<br>
> expect(result).to_equal(5.0)

</details>

</details>

#### evaluates Greek letter pi

- evaluates Greek letter pi
- evaluates Greek letter pi


<details>
<summary>Executable SSpec</summary>


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

> # @req REQ-SSPEC-FEATURE<br>
> step("evaluates Greek letter pi")<br>
> step("evaluates Greek letter pi")<br>
> val result = $? \pi$<br>
> expect(result).to_be_greater_than(3.0)

</details>

</details>

### Math Block LaTeX Export

#### exports simple arithmetic

- exports simple arithmetic
- exports simple arithmetic
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>


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

- exports fractions
- exports fractions
   - Expected: result equals `0.5`


<details>
<summary>Executable SSpec</summary>


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

- exports Greek letters
- exports Greek letters


<details>
<summary>Executable SSpec</summary>


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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-USAGE-MATH-BLOCKS-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1be6b676d537caaa02273d0259b45ede6be9df67b926f2a67c47c306a1056d30`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1be6b676d537caaa02273d0259b45ede6be9df67b926f2a67c47c306a1056d30`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1be6b676d537caaa02273d0259b45ede6be9df67b926f2a67c47c306a1056d30`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/usage/math_blocks_spec.spl
mirror: doc/06_spec/feature/usage/math_blocks_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/math_blocks_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/math_blocks_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/math_blocks_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 22 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/math_blocks_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates addition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/math_blocks_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates subtraction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/math_blocks_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates multiplication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
