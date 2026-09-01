# Math Repr Coverage Specification

> Branch coverage tests for `std.math_repr` parser and renderers. Split from math_coverage_spec.spl for memory. Tests to_text, to_debug, to_pretty, to_md, render_latex_raw, and tokenizer/parser edge cases.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 139 | 139 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Repr Coverage Specification

Branch coverage tests for `std.math_repr` parser and renderers. Split from math_coverage_spec.spl for memory. Tests to_text, to_debug, to_pretty, to_md, render_latex_raw, and tokenizer/parser edge cases.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-MATH-COV |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/common/math_repr_plain_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Branch coverage tests for `std.math_repr` parser and renderers.
Split from math_coverage_spec.spl for memory. Tests to_text, to_debug,
to_pretty, to_md, render_latex_raw, and tokenizer/parser edge cases.

## Key Concepts

| Concept | Description |
|---------|-------------|
| math_repr | Parser + renderer: to_text, to_debug, to_pretty, to_md, render_latex_raw |

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

### math_repr to_pretty

#### number literals

#### renders number unchanged

- renders number unchanged
   - Expected: to_pretty("42") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders number unchanged")
expect(to_pretty("42")).to_equal("42")
```

</details>

#### identifiers with greek resolution

#### renders plain identifier

- renders plain identifier
   - Expected: to_pretty("x") equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders plain identifier")
expect(to_pretty("x")).to_equal("x")
```

</details>

#### resolves lowercase greek

- resolves lowercase greek
   - Expected: result equals `\u03B1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves lowercase greek")
val result = to_pretty("alpha")
expect(result).to_equal("\u03B1")
```

</details>

#### resolves uppercase greek

- resolves uppercase greek
   - Expected: result equals `\u0393`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves uppercase greek")
val result = to_pretty("Gamma")
expect(result).to_equal("\u0393")
```

</details>

#### leaves non-greek identifier unchanged

- leaves non-greek identifier unchanged
   - Expected: to_pretty("foo") equals `foo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves non-greek identifier unchanged")
expect(to_pretty("foo")).to_equal("foo")
```

</details>

#### arithmetic operations

#### renders addition

- renders addition


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders addition")
expect(to_pretty("a + b")).to_contain("+")
```

</details>

#### renders subtraction

- renders subtraction


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders subtraction")
expect(to_pretty("a - b")).to_contain("-")
```

</details>

#### renders explicit multiplication

- renders explicit multiplication


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders explicit multiplication")
expect(to_pretty("a * b")).to_contain("*")
```

</details>

#### renders implicit multiplication without operator

- renders implicit multiplication without operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders implicit multiplication without operator")
val result = to_pretty("2x")
expect(result).to_contain("2")
expect(result).to_contain("x")
```

</details>

#### renders division

- renders division


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders division")
expect(to_pretty("a / b")).to_contain("/")
```

</details>

#### power rendering

#### renders power with pretty_power

- renders power with pretty_power


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders power with pretty_power")
val result = to_pretty("x^2")
expect(result).to_contain("x")
```

</details>

#### negation

#### renders negation with minus

- renders negation with minus


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders negation with minus")
expect(to_pretty("-x")).to_start_with("-")
```

</details>

#### grouping

#### renders parentheses

- renders parentheses


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders parentheses")
val result = to_pretty("(x + 1)")
expect(result).to_start_with("(")
expect(result).to_end_with(")")
```

</details>

#### subscript rendering

#### renders subscript with pretty_sub

- renders subscript with pretty_sub


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders subscript with pretty_sub")
val result = to_pretty("x[i]")
expect(result).to_contain("x")
```

</details>

#### transpose rendering

#### renders transpose with T suffix

- renders transpose with T suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders transpose with T suffix")
val result = to_pretty("A'")
expect(result).to_contain("A")
expect(result).to_contain("ᵀ")
```

</details>

#### function calls

#### renders sqrt with pretty_sqrt

- renders sqrt with pretty_sqrt


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders sqrt with pretty_sqrt")
val result = to_pretty("sqrt(x)")
expect(result).to_contain("x")
```

</details>

#### renders non-sqrt function normally

- renders non-sqrt function normally


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders non-sqrt function normally")
val result = to_pretty("sin(x)")
expect(result).to_contain("sin")
expect(result).to_contain("x")
```

</details>

#### frac rendering

#### renders fraction with pretty_fraction

- renders fraction with pretty_fraction


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders fraction with pretty_fraction")
val result = to_pretty("frac(a, b)")
expect(result).to_contain("a")
expect(result).to_contain("b")
```

</details>

#### sum and integral rendering

#### renders sum expression

- renders sum expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders sum expression")
val result = to_pretty("sum(i, 1..n) i")
expect(result).to_contain("i")
```

</details>

#### renders integral expression

- renders integral expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders integral expression")
val result = to_pretty("int(x, 0..1) x")
expect(result).to_contain("x")
```

</details>

### math_repr to_md

#### markdown wrapping and identifiers

#### wraps output in dollar signs

- wraps output in dollar signs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps output in dollar signs")
val result = to_md("x")
expect(result).to_start_with("$")
expect(result).to_end_with("$")
```

</details>

#### renders number and plain identifier

- renders number and plain identifier
   - Expected: to_md("42") equals `$42$`
   - Expected: to_md("x") equals `$x$`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders number and plain identifier")
expect(to_md("42")).to_equal("$42$")
expect(to_md("x")).to_equal("$x$")
```

</details>

#### renders greek and uppercase greek

- renders greek and uppercase greek


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders greek and uppercase greek")
expect(to_md("alpha")).to_contain("\\alpha")
expect(to_md("Gamma")).to_contain("\\Gamma")
```

</details>

#### binary operations and unary

#### renders add, sub, mul, div

- renders add, sub, mul, div


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders add, sub, mul, div")
expect(to_md("a + b")).to_contain("+")
expect(to_md("a - b")).to_contain("-")
expect(to_md("a * b")).to_contain("\\cdot")
expect(to_md("a / b")).to_contain("/")
```

</details>

#### renders implicit mul, power, negation

- renders implicit mul, power, negation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders implicit mul, power, negation")
expect(to_md("2x")).to_contain("x")
expect(to_md("x^2")).to_contain("x")
expect(to_md("-x")).to_contain("-")
```

</details>

#### grouping, subscript, transpose

#### renders grouped expression

- renders grouped expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders grouped expression")
expect(to_md("(a + b)")).to_contain("(")
```

</details>

#### renders subscript and transpose

- renders subscript and transpose


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders subscript and transpose")
expect(to_md("x[i]")).to_contain("x")
expect(to_md("A'")).to_contain('^{T}')
```

</details>

#### function calls

#### renders unknown function with operatorname

- renders unknown function with operatorname


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders unknown function with operatorname")
expect(to_md("foo(x)")).to_contain('\operatorname{foo}')
```

</details>

#### renders sqrt, known, and multi-arg functions

- renders sqrt, known, and multi-arg functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders sqrt, known, and multi-arg functions")
expect(to_md("sqrt(x)")).to_contain("x")
expect(to_md("sin(x)")).to_contain("\\sin")
expect(to_md("max(a, b)")).to_contain("\\max")
```

</details>

#### frac, sum, integral rendering

#### renders frac with latex_fraction

- renders frac with latex_fraction


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders frac with latex_fraction")
expect(to_md("frac(a, b)")).to_contain("a")
```

</details>

#### renders sum and integral

- renders sum and integral


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders sum and integral")
expect(to_md("sum(i, 1..n) i")).to_contain("i")
expect(to_md("int(x, 0..1) x")).to_contain("x")
```

</details>

### math_repr render_latex_raw

#### raw latex output

#### does not wrap in dollar signs

- does not wrap in dollar signs
   - Expected: result equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not wrap in dollar signs")
val result = render_latex_raw("x")
expect(result).to_equal("x")
```

</details>

#### renders expression without wrapping

- renders expression without wrapping


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders expression without wrapping")
val result = render_latex_raw("x + 1")
expect(result).to_contain("+")
```

</details>

### math_repr tokenizer edges

#### whitespace handling

#### handles extra spaces

- handles extra spaces
   - Expected: to_text("x  +  y") equals `x + y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles extra spaces")
expect(to_text("x  +  y")).to_equal("x + y")
```

</details>

#### handles tabs

- handles tabs
   - Expected: to_text("x\t+\ty") equals `x + y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles tabs")
expect(to_text("x\t+\ty")).to_equal("x + y")
```

</details>

#### dot and range tokens

#### handles dot-dot range in sum

- handles dot-dot range in sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles dot-dot range in sum")
val result = to_text("sum(i, 1..10) i")
expect(result).to_contain("..")
```

</details>

#### bracket tokens

#### handles square brackets for subscript

- handles square brackets for subscript
   - Expected: to_text("a[0]") equals `a[0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles square brackets for subscript")
expect(to_text("a[0]")).to_equal("a[0]")
```

</details>

#### comma tokens

#### handles commas in function args

- handles commas in function args
   - Expected: to_text("f(a, b, c)") equals `f(a, b, c)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles commas in function args")
expect(to_text("f(a, b, c)")).to_equal("f(a, b, c)")
```

</details>

#### unknown characters

#### skips unknown characters gracefully

- skips unknown characters gracefully


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips unknown characters gracefully")
val result = to_text("x + y")
expect(result).to_contain("x")
expect(result).to_contain("y")
```

</details>

#### empty input

#### handles empty string with fallback

- handles empty string with fallback
   - Expected: result equals `?`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string with fallback")
# Empty input produces eof token; parser fallback returns "?" node
val result = to_text("")
expect(result).to_equal("?")
```

</details>

### math_repr parser edges

#### operator precedence

#### mul binds tighter than add

- mul binds tighter than add
   - Expected: to_debug("a + b * c") equals `Add(Id(a), Mul(Id(b), Id(c)))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mul binds tighter than add")
expect(to_debug("a + b * c")).to_equal("Add(Id(a), Mul(Id(b), Id(c)))")
```

</details>

#### power binds tighter than mul

- power binds tighter than mul
   - Expected: to_debug("a * b^c") equals `Mul(Id(a), Pow(Id(b), Id(c)))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("power binds tighter than mul")
expect(to_debug("a * b^c")).to_equal("Mul(Id(a), Pow(Id(b), Id(c)))")
```

</details>

#### negation applies to power

- negation applies to power
   - Expected: to_debug("-x^2") equals `Neg(Pow(Id(x), Num(2)))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negation applies to power")
expect(to_debug("-x^2")).to_equal("Neg(Pow(Id(x), Num(2)))")
```

</details>

#### implicit multiplication

#### number followed by identifier

- number followed by identifier
   - Expected: to_debug("3x") equals `Mul(Num(3), Id(x))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("number followed by identifier")
expect(to_debug("3x")).to_equal("Mul(Num(3), Id(x))")
```

</details>

#### number followed by paren group

- number followed by paren group
   - Expected: to_debug("2(x)") equals `Mul(Num(2), Group(Id(x)))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("number followed by paren group")
expect(to_debug("2(x)")).to_equal("Mul(Num(2), Group(Id(x)))")
```

</details>

#### identifier followed by paren starts function call

- identifier followed by paren starts function call
   - Expected: to_debug("f(x)") equals `Call(f, Id(x))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifier followed by paren starts function call")
expect(to_debug("f(x)")).to_equal("Call(f, Id(x))")
```

</details>

#### nested grouping

#### handles nested parentheses

- handles nested parentheses
   - Expected: to_debug("((x))") equals `Group(Group(Id(x)))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles nested parentheses")
expect(to_debug("((x))")).to_equal("Group(Group(Id(x)))")
```

</details>

#### chained postfix

#### handles subscript then transpose

- handles subscript then transpose


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles subscript then transpose")
val result = to_debug("A[i]'")
expect(result).to_contain("Transpose")
expect(result).to_contain("Sub")
```

</details>

#### known function detection for latex

#### recognizes sin as known

- recognizes sin as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes sin as known")
val result = render_latex_raw("sin(x)")
expect(result).to_contain("\\sin")
```

</details>

#### recognizes cos as known

- recognizes cos as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes cos as known")
val result = render_latex_raw("cos(x)")
expect(result).to_contain("\\cos")
```

</details>

#### recognizes tan as known

- recognizes tan as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes tan as known")
val result = render_latex_raw("tan(x)")
expect(result).to_contain("\\tan")
```

</details>

#### recognizes log as known

- recognizes log as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes log as known")
val result = render_latex_raw("log(x)")
expect(result).to_contain("\\log")
```

</details>

#### recognizes ln as known

- recognizes ln as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes ln as known")
val result = render_latex_raw("ln(x)")
expect(result).to_contain("\\ln")
```

</details>

#### recognizes exp as known

- recognizes exp as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes exp as known")
val result = render_latex_raw("exp(x)")
expect(result).to_contain("\\exp")
```

</details>

#### recognizes min as known

- recognizes min as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes min as known")
val result = render_latex_raw("min(a, b)")
expect(result).to_contain("\\min")
```

</details>

#### recognizes lim as known

- recognizes lim as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes lim as known")
val result = render_latex_raw("lim(x)")
expect(result).to_contain("\\lim")
```

</details>

#### recognizes tanh as known

- recognizes tanh as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes tanh as known")
val result = render_latex_raw("tanh(x)")
expect(result).to_contain("\\tanh")
```

</details>

#### recognizes sinh as known

- recognizes sinh as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes sinh as known")
val result = render_latex_raw("sinh(x)")
expect(result).to_contain("\\sinh")
```

</details>

#### recognizes cosh as known

- recognizes cosh as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes cosh as known")
val result = render_latex_raw("cosh(x)")
expect(result).to_contain("\\cosh")
```

</details>

#### treats unknown function as operatorname

- treats unknown function as operatorname


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats unknown function as operatorname")
val result = render_latex_raw("foo(x)")
expect(result).to_contain('\operatorname{foo}')
```

</details>

#### zero-arg function call

#### renders function with no args

- renders function with no args
   - Expected: to_text("f()") equals `f()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders function with no args")
expect(to_text("f()")).to_equal("f()")
```

</details>

#### single dot token

#### handles single dot at end of input

- handles single dot at end of input


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single dot at end of input")
val result = to_text("x.")
expect(result).to_contain("x")
```

</details>

#### character coverage for _is_digit

#### exercises all digit branches 0-9

- exercises all digit branches 0-9
   - Expected: result equals `1234567890`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises all digit branches 0-9")
# Number containing all 10 digits covers every _is_digit branch
val result = to_text("1234567890")
expect(result).to_equal("1234567890")
```

</details>

#### exercises decimal number with dot

- exercises decimal number with dot
   - Expected: result equals `3.14159`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises decimal number with dot")
val result = to_text("3.14159")
expect(result).to_equal("3.14159")
```

</details>

#### character coverage for _is_alpha

#### exercises lowercase a-m in identifiers

- exercises lowercase a-m in identifiers
   - Expected: r1 equals `abcdefg`
   - Expected: r2 equals `hijklm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises lowercase a-m in identifiers")
val r1 = to_text("abcdefg")
expect(r1).to_equal("abcdefg")
val r2 = to_text("hijklm")
expect(r2).to_equal("hijklm")
```

</details>

#### exercises lowercase n-z in identifiers

- exercises lowercase n-z in identifiers
   - Expected: r1 equals `nopqr`
   - Expected: r2 equals `stuvwxyz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises lowercase n-z in identifiers")
val r1 = to_text("nopqr")
expect(r1).to_equal("nopqr")
val r2 = to_text("stuvwxyz")
expect(r2).to_equal("stuvwxyz")
```

</details>

#### exercises uppercase A-M in identifiers

- exercises uppercase A-M in identifiers
   - Expected: r1 equals `ABCDEFG`
   - Expected: r2 equals `HIJKLM`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises uppercase A-M in identifiers")
val r1 = to_text("ABCDEFG")
expect(r1).to_equal("ABCDEFG")
val r2 = to_text("HIJKLM")
expect(r2).to_equal("HIJKLM")
```

</details>

#### exercises uppercase N-Z in identifiers

- exercises uppercase N-Z in identifiers
   - Expected: r1 equals `NOPQR`
   - Expected: r2 equals `STUVWXYZ`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises uppercase N-Z in identifiers")
val r1 = to_text("NOPQR")
expect(r1).to_equal("NOPQR")
val r2 = to_text("STUVWXYZ")
expect(r2).to_equal("STUVWXYZ")
```

</details>

#### exercises underscore in identifier

- exercises underscore in identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises underscore in identifier")
# Underscore is alpha in math tokenizer; tokenizes as single ident
val result = to_text("a_b")
expect(result).to_contain("a")
```

</details>

#### _can_start_expr and _can_implicit_mul edge cases

#### no implicit mul after operator

- no implicit mul after operator
   - Expected: result equals `Add(Id(a), Num(2))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no implicit mul after operator")
# After +, next token is num - not implicit mul context
val result = to_debug("a + 2")
expect(result).to_equal("Add(Id(a), Num(2))")
```

</details>

#### implicit mul with num before lparen

- implicit mul with num before lparen


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("implicit mul with num before lparen")
val result = to_debug("3(a + b)")
expect(result).to_contain("Mul")
expect(result).to_contain("Group")
```

</details>

#### tokenizer number-dot boundary

#### handles number followed by dot-dot range

- handles number followed by dot-dot range


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles number followed by dot-dot range")
# In sum(i, 1..10), the 1 must not consume ".." as decimal
val result = to_debug("sum(i, 1..10) i")
expect(result).to_contain("Sum")
expect(result).to_contain("Num(1)")
expect(result).to_contain("Num(10)")
```

</details>

#### greek letter resolution through pretty renderer

#### resolves beta through pretty

- resolves beta through pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves beta through pretty")
expect(to_pretty("beta")).to_contain("\u03B2")
```

</details>

#### resolves gamma delta epsilon through pretty

- resolves gamma delta epsilon through pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves gamma delta epsilon through pretty")
expect(to_pretty("gamma")).to_contain("\u03B3")
expect(to_pretty("delta")).to_contain("\u03B4")
expect(to_pretty("epsilon")).to_contain("\u03B5")
```

</details>

#### resolves zeta eta theta through pretty

- resolves zeta eta theta through pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves zeta eta theta through pretty")
expect(to_pretty("zeta")).to_contain("\u03B6")
expect(to_pretty("eta")).to_contain("\u03B7")
expect(to_pretty("theta")).to_contain("\u03B8")
```

</details>

#### resolves iota kappa lambda through pretty

- resolves iota kappa lambda through pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves iota kappa lambda through pretty")
expect(to_pretty("iota")).to_contain("\u03B9")
expect(to_pretty("kappa")).to_contain("\u03BA")
expect(to_pretty("lambda")).to_contain("\u03BB")
```

</details>

#### resolves mu nu xi through pretty

- resolves mu nu xi through pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves mu nu xi through pretty")
expect(to_pretty("mu")).to_contain("\u03BC")
expect(to_pretty("nu")).to_contain("\u03BD")
expect(to_pretty("xi")).to_contain("\u03BE")
```

</details>

#### resolves omicron pi rho through pretty

- resolves omicron pi rho through pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves omicron pi rho through pretty")
expect(to_pretty("omicron")).to_contain("\u03BF")
expect(to_pretty("pi")).to_contain("\u03C0")
expect(to_pretty("rho")).to_contain("\u03C1")
```

</details>

#### resolves sigma tau upsilon through pretty

- resolves sigma tau upsilon through pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves sigma tau upsilon through pretty")
expect(to_pretty("sigma")).to_contain("\u03C3")
expect(to_pretty("tau")).to_contain("\u03C4")
expect(to_pretty("upsilon")).to_contain("\u03C5")
```

</details>

#### resolves phi chi psi omega through pretty

- resolves phi chi psi omega through pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves phi chi psi omega through pretty")
expect(to_pretty("phi")).to_contain("\u03C6")
expect(to_pretty("chi")).to_contain("\u03C7")
expect(to_pretty("psi")).to_contain("\u03C8")
expect(to_pretty("omega")).to_contain("\u03C9")
```

</details>

#### resolves variant forms through pretty

- resolves variant forms through pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves variant forms through pretty")
expect(to_pretty("varepsilon")).to_contain("\u03F5")
expect(to_pretty("vartheta")).to_contain("\u03D1")
expect(to_pretty("varphi")).to_contain("\u03D5")
expect(to_pretty("varrho")).to_contain("\u03F1")
```

</details>

#### resolves more variants and specials through pretty

- resolves more variants and specials through pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves more variants and specials through pretty")
expect(to_pretty("varpi")).to_contain("\u03D6")
expect(to_pretty("varkappa")).to_contain("\u03F0")
expect(to_pretty("partial")).to_contain("\u2202")
expect(to_pretty("nabla")).to_contain("\u2207")
```

</details>

#### uppercase greek through pretty renderer

#### resolves Delta Theta Lambda Xi through pretty

- resolves Delta Theta Lambda Xi through pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves Delta Theta Lambda Xi through pretty")
expect(to_pretty("Delta")).to_contain("\u0394")
expect(to_pretty("Theta")).to_contain("\u0398")
expect(to_pretty("Lambda")).to_contain("\u039B")
expect(to_pretty("Xi")).to_contain("\u039E")
```

</details>

#### resolves Pi Sigma Upsilon through pretty

- resolves Pi Sigma Upsilon through pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves Pi Sigma Upsilon through pretty")
expect(to_pretty("Pi")).to_contain("\u03A0")
expect(to_pretty("Sigma")).to_contain("\u03A3")
expect(to_pretty("Upsilon")).to_contain("\u03A5")
```

</details>

#### resolves Phi Psi Omega through pretty

- resolves Phi Psi Omega through pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves Phi Psi Omega through pretty")
expect(to_pretty("Phi")).to_contain("\u03A6")
expect(to_pretty("Psi")).to_contain("\u03A8")
expect(to_pretty("Omega")).to_contain("\u03A9")
```

</details>

#### greek through latex renderer

#### renders greek letters as latex commands

- renders greek letters as latex commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders greek letters as latex commands")
expect(render_latex_raw("alpha")).to_contain("\\alpha")
expect(render_latex_raw("beta")).to_contain("\\beta")
expect(render_latex_raw("gamma")).to_contain("\\gamma")
```

</details>

#### renders uppercase greek as latex commands

- renders uppercase greek as latex commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders uppercase greek as latex commands")
expect(render_latex_raw("Gamma")).to_contain("\\Gamma")
expect(render_latex_raw("Delta")).to_contain("\\Delta")
expect(render_latex_raw("Omega")).to_contain("\\Omega")
```

</details>

#### superscript char coverage through pretty power

#### exercises superscript digits 0-4 via power

- exercises superscript digits 0-4 via power


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises superscript digits 0-4 via power")
val r0 = to_pretty("x^0")
expect(r0).to_contain("x")
val r1 = to_pretty("x^1")
expect(r1).to_contain("x")
val r3 = to_pretty("x^3")
expect(r3).to_contain("x")
val r4 = to_pretty("x^4")
expect(r4).to_contain("x")
```

</details>

#### exercises superscript digits 5-9 via power

- exercises superscript digits 5-9 via power


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises superscript digits 5-9 via power")
val r5 = to_pretty("x^5")
expect(r5).to_contain("x")
val r6 = to_pretty("x^6")
expect(r6).to_contain("x")
val r7 = to_pretty("x^7")
expect(r7).to_contain("x")
val r8 = to_pretty("x^8")
expect(r8).to_contain("x")
val r9 = to_pretty("x^9")
expect(r9).to_contain("x")
```

</details>

#### exercises superscript letters n i x via power

- exercises superscript letters n i x via power


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises superscript letters n i x via power")
val rn = to_pretty("x^n")
expect(rn).to_contain("x")
val ri = to_pretty("x^i")
expect(ri).to_contain("x")
```

</details>

#### subscript char coverage through pretty subscript

#### exercises subscript digits 0-4

- exercises subscript digits 0-4


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises subscript digits 0-4")
val r0 = to_pretty("x[0]")
expect(r0).to_contain("x")
val r1 = to_pretty("x[1]")
expect(r1).to_contain("x")
val r2 = to_pretty("x[2]")
expect(r2).to_contain("x")
val r3 = to_pretty("x[3]")
expect(r3).to_contain("x")
val r4 = to_pretty("x[4]")
expect(r4).to_contain("x")
```

</details>

#### exercises subscript digits 5-9

- exercises subscript digits 5-9


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises subscript digits 5-9")
val r5 = to_pretty("x[5]")
expect(r5).to_contain("x")
val r6 = to_pretty("x[6]")
expect(r6).to_contain("x")
val r7 = to_pretty("x[7]")
expect(r7).to_contain("x")
val r8 = to_pretty("x[8]")
expect(r8).to_contain("x")
val r9 = to_pretty("x[9]")
expect(r9).to_contain("x")
```

</details>

#### exercises subscript letters a e o x

- exercises subscript letters a e o x


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises subscript letters a e o x")
val ra = to_pretty("x[a]")
expect(ra).to_contain("x")
val re = to_pretty("x[e]")
expect(re).to_contain("x")
val ro = to_pretty("x[o]")
expect(ro).to_contain("x")
```

</details>

#### exercises subscript letters h k l m n p s t

- exercises subscript letters h k l m n p s t


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises subscript letters h k l m n p s t")
val rh = to_pretty("x[h]")
expect(rh).to_contain("x")
val rk = to_pretty("x[k]")
expect(rk).to_contain("x")
val rl = to_pretty("x[l]")
expect(rl).to_contain("x")
val rm2 = to_pretty("x[m]")
expect(rm2).to_contain("x")
val rn = to_pretty("x[n]")
expect(rn).to_contain("x")
val rp = to_pretty("x[p]")
expect(rp).to_contain("x")
val rs = to_pretty("x[s]")
expect(rs).to_contain("x")
val rt = to_pretty("x[t]")
expect(rt).to_contain("x")
```

</details>

#### exercises subscript letters i j r

- exercises subscript letters i j r


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises subscript letters i j r")
val ri = to_pretty("x[j]")
expect(ri).to_contain("x")
val rr = to_pretty("x[r]")
expect(rr).to_contain("x")
```

</details>

### math_repr empty input fallbacks

#### empty string fallback for each API function

#### to_debug handles empty string

- to_debug handles empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_debug handles empty string")
val result = to_debug("")
expect(result).to_contain("?")
```

</details>

#### to_pretty handles empty string

- to_pretty handles empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_pretty handles empty string")
val result = to_pretty("")
expect(result).to_contain("?")
```

</details>

#### to_md handles empty string

- to_md handles empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_md handles empty string")
val result = to_md("")
expect(result).to_start_with("$")
```

</details>

#### render_latex_raw handles empty string

- render_latex_raw handles empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("render_latex_raw handles empty string")
val result = render_latex_raw("")
expect(result).to_contain("?")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 139 |
| Active scenarios | 139 |
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

- Canonical SPipe generation for source `c374f486f5eb21f85cf36b5340e873e695fa359be84490957c49a1b29c20d1a7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c374f486f5eb21f85cf36b5340e873e695fa359be84490957c49a1b29c20d1a7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c374f486f5eb21f85cf36b5340e873e695fa359be84490957c49a1b29c20d1a7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/math_repr_plain_coverage_spec.spl
mirror: doc/06_spec/01_unit/lib/common/math_repr_plain_coverage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/math_repr_plain_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/math_repr_plain_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/math_repr_plain_coverage_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders integer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math_repr_plain_coverage_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders decimal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math_repr_plain_coverage_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders plain identifier' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
