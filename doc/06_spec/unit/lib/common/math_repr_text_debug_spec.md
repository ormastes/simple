# Math Repr Text and Debug Rendering

> Tests for to_text and to_debug renderers across all AST node types.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Repr Text and Debug Rendering

Tests for to_text and to_debug renderers across all AST node types.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-MATH-COV |
| Category | Stdlib |
| Status | Implemented |
| Source | `test/unit/lib/common/math_repr_text_debug_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for to_text and to_debug renderers across all AST node types.

## Scenarios

### math_repr to_text

#### number literals

#### renders integer

- renders integer
   - Expected: to_text("42") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders integer")
expect(to_text("42")).to_equal("42")
```

</details>

#### renders decimal

- renders decimal
   - Expected: to_text("3.14") equals `3.14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders decimal")
expect(to_text("3.14")).to_equal("3.14")
```

</details>

#### identifiers

#### renders plain identifier

- renders plain identifier
   - Expected: to_text("x") equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders plain identifier")
expect(to_text("x")).to_equal("x")
```

</details>

#### renders multi-char identifier

- renders multi-char identifier
   - Expected: to_text("foo") equals `foo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders multi-char identifier")
expect(to_text("foo")).to_equal("foo")
```

</details>

#### addition and subtraction

#### renders addition

- renders addition
   - Expected: to_text("x + 1") equals `x + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders addition")
expect(to_text("x + 1")).to_equal("x + 1")
```

</details>

#### renders subtraction

- renders subtraction
   - Expected: to_text("x - 1") equals `x - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders subtraction")
expect(to_text("x - 1")).to_equal("x - 1")
```

</details>

#### renders chained addition

- renders chained addition
   - Expected: to_text("a + b + c") equals `a + b + c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders chained addition")
expect(to_text("a + b + c")).to_equal("a + b + c")
```

</details>

#### multiplication and division

#### renders explicit multiplication

- renders explicit multiplication
   - Expected: to_text("x * y") equals `x * y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders explicit multiplication")
expect(to_text("x * y")).to_equal("x * y")
```

</details>

#### renders division

- renders division
   - Expected: to_text("x / y") equals `x / y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders division")
expect(to_text("x / y")).to_equal("x / y")
```

</details>

#### renders implicit multiplication

- renders implicit multiplication
   - Expected: to_text("2x") equals `2x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders implicit multiplication")
expect(to_text("2x")).to_equal("2x")
```

</details>

#### power

#### renders power expression

- renders power expression
   - Expected: to_text("x^2") equals `x^2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders power expression")
expect(to_text("x^2")).to_equal("x^2")
```

</details>

#### renders nested power

- renders nested power
   - Expected: to_text("x^y") equals `x^y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders nested power")
expect(to_text("x^y")).to_equal("x^y")
```

</details>

#### negation

#### renders negation

- renders negation
   - Expected: to_text("-x") equals `-x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders negation")
expect(to_text("-x")).to_equal("-x")
```

</details>

#### renders negation of number

- renders negation of number
   - Expected: to_text("-3") equals `-3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders negation of number")
expect(to_text("-3")).to_equal("-3")
```

</details>

#### grouping

#### renders parenthesized expression

- renders parenthesized expression
   - Expected: to_text("(x + 1)") equals `(x + 1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders parenthesized expression")
expect(to_text("(x + 1)")).to_equal("(x + 1)")
```

</details>

#### subscript

#### renders subscript notation

- renders subscript notation
   - Expected: to_text("x[i]") equals `x[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders subscript notation")
expect(to_text("x[i]")).to_equal("x[i]")
```

</details>

#### transpose

#### renders transpose

- renders transpose
   - Expected: to_text("A'") equals `A'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders transpose")
expect(to_text("A'")).to_equal("A'")
```

</details>

#### function calls

#### renders single arg function

- renders single arg function
   - Expected: to_text("sin(x)") equals `sin(x)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders single arg function")
expect(to_text("sin(x)")).to_equal("sin(x)")
```

</details>

#### renders multi arg function

- renders multi arg function
   - Expected: to_text("max(a, b)") equals `max(a, b)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders multi arg function")
expect(to_text("max(a, b)")).to_equal("max(a, b)")
```

</details>

#### frac expression

#### renders fraction as division

- renders fraction as division
   - Expected: to_text("frac(a, b)") equals `a / b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders fraction as division")
expect(to_text("frac(a, b)")).to_equal("a / b")
```

</details>

#### sum expression

#### renders sum notation

- renders sum notation
   - Expected: to_text("sum(i, 1..n) i") equals `sum(i, 1..n) i`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders sum notation")
expect(to_text("sum(i, 1..n) i")).to_equal("sum(i, 1..n) i")
```

</details>

#### int expression

#### renders integral notation

- renders integral notation
   - Expected: to_text("int(x, 0..1) x") equals `int(x, 0..1) x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders integral notation")
expect(to_text("int(x, 0..1) x")).to_equal("int(x, 0..1) x")
```

</details>

#### complex expressions

#### renders compound expression

- renders compound expression
   - Expected: to_text("x^2 + 2*x + 1") equals `x^2 + 2 * x + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders compound expression")
expect(to_text("x^2 + 2*x + 1")).to_equal("x^2 + 2 * x + 1")
```

</details>

### math_repr to_debug

#### leaf nodes

#### renders number node

- renders number node
   - Expected: to_debug("42") equals `Num(42)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders number node")
expect(to_debug("42")).to_equal("Num(42)")
```

</details>

#### renders identifier node

- renders identifier node
   - Expected: to_debug("x") equals `Id(x)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders identifier node")
expect(to_debug("x")).to_equal("Id(x)")
```

</details>

#### binary operations

#### renders Add node

- renders Add node
   - Expected: to_debug("a + b") equals `Add(Id(a), Id(b))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders Add node")
expect(to_debug("a + b")).to_equal("Add(Id(a), Id(b))")
```

</details>

#### renders Sub node

- renders Sub node
   - Expected: to_debug("a - b") equals `Sub(Id(a), Id(b))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders Sub node")
expect(to_debug("a - b")).to_equal("Sub(Id(a), Id(b))")
```

</details>

#### renders Mul node

- renders Mul node
   - Expected: to_debug("a * b") equals `Mul(Id(a), Id(b))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders Mul node")
expect(to_debug("a * b")).to_equal("Mul(Id(a), Id(b))")
```

</details>

#### renders Div node

- renders Div node
   - Expected: to_debug("a / b") equals `Div(Id(a), Id(b))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders Div node")
expect(to_debug("a / b")).to_equal("Div(Id(a), Id(b))")
```

</details>

#### renders Pow node

- renders Pow node
   - Expected: to_debug("a^b") equals `Pow(Id(a), Id(b))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders Pow node")
expect(to_debug("a^b")).to_equal("Pow(Id(a), Id(b))")
```

</details>

#### unary operations

#### renders Neg node

- renders Neg node
   - Expected: to_debug("-x") equals `Neg(Id(x))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders Neg node")
expect(to_debug("-x")).to_equal("Neg(Id(x))")
```

</details>

#### grouping

#### renders Group node

- renders Group node
   - Expected: to_debug("(x)") equals `Group(Id(x))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders Group node")
expect(to_debug("(x)")).to_equal("Group(Id(x))")
```

</details>

#### subscript and transpose

#### renders subscript as Sub

- renders subscript as Sub
   - Expected: to_debug("x[i]") equals `Sub(Id(x), Id(i))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders subscript as Sub")
expect(to_debug("x[i]")).to_equal("Sub(Id(x), Id(i))")
```

</details>

#### renders Transpose node

- renders Transpose node
   - Expected: to_debug("A'") equals `Transpose(Id(A))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders Transpose node")
expect(to_debug("A'")).to_equal("Transpose(Id(A))")
```

</details>

#### function calls

#### renders Call node

- renders Call node
   - Expected: to_debug("f(x)") equals `Call(f, Id(x))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders Call node")
expect(to_debug("f(x)")).to_equal("Call(f, Id(x))")
```

</details>

#### renders Call with multiple args

- renders Call with multiple args
   - Expected: to_debug("f(x, y)") equals `Call(f, Id(x), Id(y))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders Call with multiple args")
expect(to_debug("f(x, y)")).to_equal("Call(f, Id(x), Id(y))")
```

</details>

#### frac expression

#### renders Frac node

- renders Frac node
   - Expected: to_debug("frac(a, b)") equals `Frac(Id(a), Id(b))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders Frac node")
expect(to_debug("frac(a, b)")).to_equal("Frac(Id(a), Id(b))")
```

</details>

#### sum and integral expressions

#### renders Sum node

- renders Sum node
   - Expected: to_debug("sum(i, 1..n) i") equals `Sum(i, Num(1), Id(n), Id(i))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders Sum node")
expect(to_debug("sum(i, 1..n) i")).to_equal("Sum(i, Num(1), Id(n), Id(i))")
```

</details>

#### renders Int node

- renders Int node
   - Expected: to_debug("int(x, 0..1) x") equals `Int(x, Num(0), Num(1), Id(x))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders Int node")
expect(to_debug("int(x, 0..1) x")).to_equal("Int(x, Num(0), Num(1), Id(x))")
```

</details>

#### implicit multiplication

#### renders implicit mul as Mul

- renders implicit mul as Mul
   - Expected: to_debug("2x") equals `Mul(Num(2), Id(x))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders implicit mul as Mul")
expect(to_debug("2x")).to_equal("Mul(Num(2), Id(x))")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `07a464b8fd3f8105bfcff0de3c7963406b20d97ebf46fc898cc5c43cf47a9ae4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `07a464b8fd3f8105bfcff0de3c7963406b20d97ebf46fc898cc5c43cf47a9ae4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `07a464b8fd3f8105bfcff0de3c7963406b20d97ebf46fc898cc5c43cf47a9ae4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/math_repr_text_debug_spec.spl
mirror: doc/06_spec/unit/lib/common/math_repr_text_debug_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/math_repr_text_debug_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/math_repr_text_debug_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/math_repr_text_debug_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders integer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/math_repr_text_debug_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders decimal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/math_repr_text_debug_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders plain identifier' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
