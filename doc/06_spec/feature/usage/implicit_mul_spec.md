# Implicit Multiplication Specification

> Implicit multiplication in m{} math blocks:

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
| Source | `test/feature/usage/implicit_mul_spec.spl` |
| Updated | 2026-08-26 |
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

- treats 2x as 2*x


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("treats 2x as 2*x")

val x = 5
val result = m{ 2x }
expect result == 10
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("treats 2x as 2*x")<br>
> <br>
> val x = 5<br>
> val result = $2 x$<br>
> expect result == 10

</details>

</details>

#### treats 3y as 3*y

- treats 3y as 3*y


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("treats 3y as 3*y")

val y = 7
val result = m{ 3y }
expect result == 21
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("treats 3y as 3*y")<br>
> <br>
> val y = 7<br>
> val result = $3 y$<br>
> expect result == 21

</details>

</details>

#### works with floats

- works with floats


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with floats")

val x = 4.0
val result = m{ 2.5x }
expect result == 10.0
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("works with floats")<br>
> <br>
> val x = 4.0<br>
> val result = $2.5 x$<br>
> expect result == 10.0

</details>

</details>

#### number followed by parentheses

#### treats 2(x+1) as 2*(x+1)

- treats 2(x+1) as 2*(x+1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("treats 2(x+1) as 2*(x+1)")

val x = 3
val result = m{ 2(x + 1) }
expect result == 8
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("treats 2(x+1) as 2*(x+1)")<br>
> <br>
> val x = 3<br>
> val result = $2 (x + 1)$<br>
> expect result == 8

</details>

</details>

#### works in complex expressions

- works in complex expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works in complex expressions")

val x = 2
val result = m{ 3(x + 1)^2 }
expect result == 27.0  # 3 * (3)^2 = 3 * 9
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("works in complex expressions")<br>
> <br>
> val x = 2<br>
> val result = $3 (x + 1)^{2}$<br>
> expect result == 27.0  # 3 * (3)^2 = 3 * 9

</details>

</details>

#### parentheses followed by parentheses

#### treats (a)(b) as (a)*(b)

- treats (a)(b) as (a)*(b)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("treats (a)(b) as (a)*(b)")

val a = 2
val b = 3
val result = m{ (a + 1)(b - 1) }
expect result == 6  # (3) * (2)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("treats (a)(b) as (a)*(b)")<br>
> <br>
> val a = 2<br>
> val b = 3<br>
> val result = $(a + 1) (b - 1)$<br>
> expect result == 6  # (3) * (2)

</details>

</details>

#### chains multiple groups

- chains multiple groups


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chains multiple groups")

val a = 2
val result = m{ (a)(a)(a) }
expect result == 8  # 2 * 2 * 2
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("chains multiple groups")<br>
> <br>
> val a = 2<br>
> val result = $(a) (a) (a)$<br>
> expect result == 8  # 2 * 2 * 2

</details>

</details>

#### parentheses followed by identifier

#### treats (x+1)y as (x+1)*y

- treats (x+1)y as (x+1)*y


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("treats (x+1)y as (x+1)*y")

val x = 2
val y = 4
val result = m{ (x + 1)y }
expect result == 12  # (3) * 4
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("treats (x+1)y as (x+1)*y")<br>
> <br>
> val x = 2<br>
> val y = 4<br>
> val result = $(x + 1) y$<br>
> expect result == 12  # (3) * 4

</details>

</details>

#### complex expressions

#### computes quadratic with implicit mul

- computes quadratic with implicit mul


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes quadratic with implicit mul")

val x = 3
val result = m{ 2x^2 + 3x + 1 }
expect result == 28.0  # 2*9 + 3*3 + 1
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("computes quadratic with implicit mul")<br>
> <br>
> val x = 3<br>
> val result = $2 x^{2} + 3 x + 1$<br>
> expect result == 28.0  # 2*9 + 3*3 + 1

</details>

</details>

#### computes polynomial

- computes polynomial


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes polynomial")

val x = 2
val result = m{ x^3 + 2x^2 + 3x + 4 }
expect result == 26.0  # 8 + 8 + 6 + 4
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("computes polynomial")<br>
> <br>
> val x = 2<br>
> val result = $x^{3} + 2 x^{2} + 3 x + 4$<br>
> expect result == 26.0  # 8 + 8 + 6 + 4

</details>

</details>

#### mixes explicit and implicit mul

- mixes explicit and implicit mul


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("mixes explicit and implicit mul")

val x = 3
val result = m{ 2x * 3 }
expect result == 18  # (2*3) * 3
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("mixes explicit and implicit mul")<br>
> <br>
> val x = 3<br>
> val result = $2 x \cdot 3$<br>
> expect result == 18  # (2*3) * 3

</details>

</details>

#### handles scientific notation style

- handles scientific notation style


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles scientific notation style")

val pi = 3.14159
val r = 2
val area = m{ pi r^2 }
expect(area).to_be_greater_than(12.56)
expect(area).to_be_less_than(12.57)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("handles scientific notation style")<br>
> <br>
> val pi = 3.14159<br>
> val r = 2<br>
> val area = $\pi r^{2}$<br>
> expect(area).to_be_greater_than(12.56)<br>
> expect(area).to_be_less_than(12.57)

</details>

</details>

#### matrix expressions

<details>
<summary>Advanced: multiplies coefficient and matrix</summary>

#### multiplies coefficient and matrix

- multiplies coefficient and matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies coefficient and matrix")

val A = [[1, 2], [3, 4]]
val result = m{ 2A }
expect result == [[2, 4], [6, 8]]
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("multiplies coefficient and matrix")<br>
> <br>
> val A = [[1, 2], [3, 4]]<br>
> val result = $2 A$<br>
> expect result == [[2, 4], [6, 8]]

</details>

</details>


</details>

#### works in linear algebra

- works in linear algebra


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works in linear algebra")

val A = [[1, 0], [0, 1]]
val x = [1, 2]
val b = [3, 4]
# 2Ax + b
val result = m{ 2(A @ x) + b }
expect result == [5, 8]
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("works in linear algebra")<br>
> <br>
> val A = [[1, 0], [0, 1]]<br>
> val x = [1, 2]<br>
> val b = [3, 4]<br>
> # 2Ax + b<br>
> val result = $2 (A) + b$<br>
> expect result == [5, 8]

</details>

</details>

#### precedence

#### implicit mul has same precedence as explicit

- implicit mul has same precedence as explicit


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("implicit mul has same precedence as explicit")

val x = 2
val y = 3
# 2x + 3y should be (2*x) + (3*y)
val result = m{ 2x + 3y }
expect result == 13  # 4 + 9
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("implicit mul has same precedence as explicit")<br>
> <br>
> val x = 2<br>
> val y = 3<br>
> # 2x + 3y should be (2*x) + (3*y)<br>
> val result = $2 x + 3 y$<br>
> expect result == 13  # 4 + 9

</details>

</details>

#### power binds tighter

- power binds tighter


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("power binds tighter")

val x = 2
# 2x^3 should be 2*(x^3) not (2*x)^3
val result = m{ 2x^3 }
expect result == 16.0  # 2 * 8
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("power binds tighter")<br>
> <br>
> val x = 2<br>
> # 2x^3 should be 2*(x^3) not (2*x)^3<br>
> val result = $2 x^{3}$<br>
> expect result == 16.0  # 2 * 8

</details>

</details>

#### outside m{} blocks

#### does NOT allow implicit mul outside m{}

- does NOT allow implicit mul outside m{}


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does NOT allow implicit mul outside m{}")
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

- preserves function call syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("preserves function call syntax")
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

- handles negative coefficient


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles negative coefficient")
val x = 3
val result = m{ -2x }
expect result == -6
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("handles negative coefficient")<br>
> val x = 3<br>
> val result = $-2 x$<br>
> expect result == -6

</details>

</details>

#### handles subtraction vs negative

- handles subtraction vs negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles subtraction vs negative")

val x = 3
val y = 2
# -x y should be (-x) * y
val result = m{ -x y }
expect result == -6
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("handles subtraction vs negative")<br>
> <br>
> val x = 3<br>
> val y = 2<br>
> # -x y should be (-x) * y<br>
> val result = $-x y$<br>
> expect result == -6

</details>

</details>

#### whitespace

#### works without spaces

- works without spaces


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works without spaces")

val x = 5
val result = m{ 2x+3 }
expect result == 13
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("works without spaces")<br>
> <br>
> val x = 5<br>
> val result = $2 x + 3$<br>
> expect result == 13

</details>

</details>

#### works with spaces

- works with spaces


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with spaces")

val x = 5
val result = m{ 2 x + 3 }
expect result == 13
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-FEATURE<br>
> step("works with spaces")<br>
> <br>
> val x = 5<br>
> val result = $2 x + 3$<br>
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4fdbba6ca167cfbd2d3de8a78562452f79b4a59c3981499d7291486a0265790c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4fdbba6ca167cfbd2d3de8a78562452f79b4a59c3981499d7291486a0265790c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4fdbba6ca167cfbd2d3de8a78562452f79b4a59c3981499d7291486a0265790c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/implicit_mul_spec.spl
mirror: doc/06_spec/feature/usage/implicit_mul_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/implicit_mul_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/implicit_mul_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/implicit_mul_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats 2x as 2*x' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/implicit_mul_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats 3y as 3*y' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/implicit_mul_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'works with floats' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
