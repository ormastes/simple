# Math Repr Coverage Specification

> Branch coverage tests for `std.math_repr` parser and renderers. Split from math_coverage_spec.spl for memory. Tests to_text, to_debug, to_pretty, to_md, render_latex_raw, and tokenizer/parser edge cases.

<!-- sdn-diagram:id=math_repr_plain_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_repr_plain_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_repr_plain_coverage_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_repr_plain_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("42")).to_equal("42")
```

</details>

#### renders decimal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("3.14")).to_equal("3.14")
```

</details>

#### identifiers

#### renders plain identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("x")).to_equal("x")
```

</details>

#### renders multi-char identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("foo")).to_equal("foo")
```

</details>

#### addition and subtraction

#### renders addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("x + 1")).to_equal("x + 1")
```

</details>

#### renders subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("x - 1")).to_equal("x - 1")
```

</details>

#### renders chained addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("a + b + c")).to_equal("a + b + c")
```

</details>

#### multiplication and division

#### renders explicit multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("x * y")).to_equal("x * y")
```

</details>

#### renders division

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("x / y")).to_equal("x / y")
```

</details>

#### renders implicit multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("2x")).to_equal("2x")
```

</details>

#### power

#### renders power expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("x^2")).to_equal("x^2")
```

</details>

#### renders nested power

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("x^y")).to_equal("x^y")
```

</details>

#### negation

#### renders negation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("-x")).to_equal("-x")
```

</details>

#### renders negation of number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("-3")).to_equal("-3")
```

</details>

#### grouping

#### renders parenthesized expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("(x + 1)")).to_equal("(x + 1)")
```

</details>

#### subscript

#### renders subscript notation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("x[i]")).to_equal("x[i]")
```

</details>

#### transpose

#### renders transpose

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("A'")).to_equal("A'")
```

</details>

#### function calls

#### renders single arg function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("sin(x)")).to_equal("sin(x)")
```

</details>

#### renders multi arg function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("max(a, b)")).to_equal("max(a, b)")
```

</details>

#### frac expression

#### renders fraction as division

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("frac(a, b)")).to_equal("a / b")
```

</details>

#### sum expression

#### renders sum notation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("sum(i, 1..n) i")).to_equal("sum(i, 1..n) i")
```

</details>

#### int expression

#### renders integral notation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("int(x, 0..1) x")).to_equal("int(x, 0..1) x")
```

</details>

#### complex expressions

#### renders compound expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("x^2 + 2*x + 1")).to_equal("x^2 + 2 * x + 1")
```

</details>

### math_repr to_debug

#### leaf nodes

#### renders number node

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("42")).to_equal("Num(42)")
```

</details>

#### renders identifier node

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("x")).to_equal("Id(x)")
```

</details>

#### binary operations

#### renders Add node

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("a + b")).to_equal("Add(Id(a), Id(b))")
```

</details>

#### renders Sub node

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("a - b")).to_equal("Sub(Id(a), Id(b))")
```

</details>

#### renders Mul node

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("a * b")).to_equal("Mul(Id(a), Id(b))")
```

</details>

#### renders Div node

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("a / b")).to_equal("Div(Id(a), Id(b))")
```

</details>

#### renders Pow node

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("a^b")).to_equal("Pow(Id(a), Id(b))")
```

</details>

#### unary operations

#### renders Neg node

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("-x")).to_equal("Neg(Id(x))")
```

</details>

#### grouping

#### renders Group node

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("(x)")).to_equal("Group(Id(x))")
```

</details>

#### subscript and transpose

#### renders subscript as Sub

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("x[i]")).to_equal("Sub(Id(x), Id(i))")
```

</details>

#### renders Transpose node

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("A'")).to_equal("Transpose(Id(A))")
```

</details>

#### function calls

#### renders Call node

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("f(x)")).to_equal("Call(f, Id(x))")
```

</details>

#### renders Call with multiple args

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("f(x, y)")).to_equal("Call(f, Id(x), Id(y))")
```

</details>

#### frac expression

#### renders Frac node

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("frac(a, b)")).to_equal("Frac(Id(a), Id(b))")
```

</details>

#### sum and integral expressions

#### renders Sum node

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("sum(i, 1..n) i")).to_equal("Sum(i, Num(1), Id(n), Id(i))")
```

</details>

#### renders Int node

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("int(x, 0..1) x")).to_equal("Int(x, Num(0), Num(1), Id(x))")
```

</details>

#### implicit multiplication

#### renders implicit mul as Mul

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("2x")).to_equal("Mul(Num(2), Id(x))")
```

</details>

### math_repr to_pretty

#### number literals

#### renders number unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("42")).to_equal("42")
```

</details>

#### identifiers with greek resolution

#### renders plain identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("x")).to_equal("x")
```

</details>

#### resolves lowercase greek

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("alpha")
expect(result).to_equal("\u03B1")
```

</details>

#### resolves uppercase greek

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("Gamma")
expect(result).to_equal("\u0393")
```

</details>

#### leaves non-greek identifier unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("foo")).to_equal("foo")
```

</details>

#### arithmetic operations

#### renders addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("a + b")).to_contain("+")
```

</details>

#### renders subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("a - b")).to_contain("-")
```

</details>

#### renders explicit multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("a * b")).to_contain("*")
```

</details>

#### renders implicit multiplication without operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("2x")
expect(result).to_contain("2")
expect(result).to_contain("x")
```

</details>

#### renders division

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("a / b")).to_contain("/")
```

</details>

#### power rendering

#### renders power with pretty_power

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("x^2")
expect(result).to_contain("x")
```

</details>

#### negation

#### renders negation with minus

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("-x")).to_start_with("-")
```

</details>

#### grouping

#### renders parentheses

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("(x + 1)")
expect(result).to_start_with("(")
expect(result).to_end_with(")")
```

</details>

#### subscript rendering

#### renders subscript with pretty_sub

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("x[i]")
expect(result).to_contain("x")
```

</details>

#### transpose rendering

#### renders transpose with T suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("A'")
expect(result).to_contain("A")
expect(result).to_contain("T")
```

</details>

#### function calls

#### renders sqrt with pretty_sqrt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("sqrt(x)")
expect(result).to_contain("x")
```

</details>

#### renders non-sqrt function normally

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("sin(x)")
expect(result).to_contain("sin")
expect(result).to_contain("x")
```

</details>

#### frac rendering

#### renders fraction with pretty_fraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("frac(a, b)")
expect(result).to_contain("a")
expect(result).to_contain("b")
```

</details>

#### sum and integral rendering

#### renders sum expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("sum(i, 1..n) i")
expect(result).to_contain("i")
```

</details>

#### renders integral expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("int(x, 0..1) x")
expect(result).to_contain("x")
```

</details>

### math_repr to_md

#### markdown wrapping and identifiers

#### wraps output in dollar signs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_md("x")
expect(result).to_start_with("$")
expect(result).to_end_with("$")
```

</details>

#### renders number and plain identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_md("42")).to_equal("$42$")
expect(to_md("x")).to_equal("$x$")
```

</details>

#### renders greek and uppercase greek

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_md("alpha")).to_contain("\\alpha")
expect(to_md("Gamma")).to_contain("\\Gamma")
```

</details>

#### binary operations and unary

#### renders add, sub, mul, div

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_md("a + b")).to_contain("+")
expect(to_md("a - b")).to_contain("-")
expect(to_md("a * b")).to_contain("\\cdot")
expect(to_md("a / b")).to_contain("/")
```

</details>

#### renders implicit mul, power, negation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_md("2x")).to_contain("x")
expect(to_md("x^2")).to_contain("x")
expect(to_md("-x")).to_contain("-")
```

</details>

#### grouping, subscript, transpose

#### renders grouped expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_md("(a + b)")).to_contain("(")
```

</details>

#### renders subscript and transpose

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_md("x[i]")).to_contain("x")
expect(to_md("A'")).to_contain('^{T}')
```

</details>

#### function calls

#### renders unknown function with operatorname

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_md("foo(x)")).to_contain('\operatorname{foo}')
```

</details>

#### renders sqrt, known, and multi-arg functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_md("sqrt(x)")).to_contain("x")
expect(to_md("sin(x)")).to_contain("\\sin")
expect(to_md("max(a, b)")).to_contain("\\max")
```

</details>

#### frac, sum, integral rendering

#### renders frac with latex_fraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_md("frac(a, b)")).to_contain("a")
```

</details>

#### renders sum and integral

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_md("sum(i, 1..n) i")).to_contain("i")
expect(to_md("int(x, 0..1) x")).to_contain("x")
```

</details>

### math_repr render_latex_raw

#### raw latex output

#### does not wrap in dollar signs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("x")
expect(result).to_equal("x")
```

</details>

#### renders expression without wrapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("x + 1")
expect(result).to_contain("+")
```

</details>

### math_repr tokenizer edges

#### whitespace handling

#### handles extra spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("x  +  y")).to_equal("x + y")
```

</details>

#### handles tabs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("x\t+\ty")).to_equal("x + y")
```

</details>

#### dot and range tokens

#### handles dot-dot range in sum

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("sum(i, 1..10) i")
expect(result).to_contain("..")
```

</details>

#### bracket tokens

#### handles square brackets for subscript

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("a[0]")).to_equal("a[0]")
```

</details>

#### comma tokens

#### handles commas in function args

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("f(a, b, c)")).to_equal("f(a, b, c)")
```

</details>

#### unknown characters

#### skips unknown characters gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("x + y")
expect(result).to_contain("x")
expect(result).to_contain("y")
```

</details>

#### empty input

#### handles empty string with fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Empty input produces eof token; parser fallback returns "?" node
val result = to_text("")
expect(result).to_equal("?")
```

</details>

### math_repr parser edges

#### operator precedence

#### mul binds tighter than add

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("a + b * c")).to_equal("Add(Id(a), Mul(Id(b), Id(c)))")
```

</details>

#### power binds tighter than mul

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("a * b^c")).to_equal("Mul(Id(a), Pow(Id(b), Id(c)))")
```

</details>

#### negation applies to power

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("-x^2")).to_equal("Neg(Pow(Id(x), Num(2)))")
```

</details>

#### implicit multiplication

#### number followed by identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("3x")).to_equal("Mul(Num(3), Id(x))")
```

</details>

#### number followed by paren group

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("2(x)")).to_equal("Mul(Num(2), Group(Id(x)))")
```

</details>

#### identifier followed by paren starts function call

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("f(x)")).to_equal("Call(f, Id(x))")
```

</details>

#### nested grouping

#### handles nested parentheses

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("((x))")).to_equal("Group(Group(Id(x)))")
```

</details>

#### chained postfix

#### handles subscript then transpose

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("A[i]'")
expect(result).to_contain("Transpose")
expect(result).to_contain("Sub")
```

</details>

#### known function detection for latex

#### recognizes sin as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("sin(x)")
expect(result).to_contain("\\sin")
```

</details>

#### recognizes cos as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("cos(x)")
expect(result).to_contain("\\cos")
```

</details>

#### recognizes tan as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("tan(x)")
expect(result).to_contain("\\tan")
```

</details>

#### recognizes log as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("log(x)")
expect(result).to_contain("\\log")
```

</details>

#### recognizes ln as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("ln(x)")
expect(result).to_contain("\\ln")
```

</details>

#### recognizes exp as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("exp(x)")
expect(result).to_contain("\\exp")
```

</details>

#### recognizes min as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("min(a, b)")
expect(result).to_contain("\\min")
```

</details>

#### recognizes lim as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("lim(x)")
expect(result).to_contain("\\lim")
```

</details>

#### recognizes tanh as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("tanh(x)")
expect(result).to_contain("\\tanh")
```

</details>

#### recognizes sinh as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("sinh(x)")
expect(result).to_contain("\\sinh")
```

</details>

#### recognizes cosh as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("cosh(x)")
expect(result).to_contain("\\cosh")
```

</details>

#### treats unknown function as operatorname

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("foo(x)")
expect(result).to_contain('\operatorname{foo}')
```

</details>

#### zero-arg function call

#### renders function with no args

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("f()")).to_equal("f()")
```

</details>

#### single dot token

#### handles single dot at end of input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("x.")
expect(result).to_contain("x")
```

</details>

#### character coverage for _is_digit

#### exercises all digit branches 0-9

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Number containing all 10 digits covers every _is_digit branch
val result = to_text("1234567890")
expect(result).to_equal("1234567890")
```

</details>

#### exercises decimal number with dot

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("3.14159")
expect(result).to_equal("3.14159")
```

</details>

#### character coverage for _is_alpha

#### exercises lowercase a-m in identifiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = to_text("abcdefg")
expect(r1).to_equal("abcdefg")
val r2 = to_text("hijklm")
expect(r2).to_equal("hijklm")
```

</details>

#### exercises lowercase n-z in identifiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = to_text("nopqr")
expect(r1).to_equal("nopqr")
val r2 = to_text("stuvwxyz")
expect(r2).to_equal("stuvwxyz")
```

</details>

#### exercises uppercase A-M in identifiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = to_text("ABCDEFG")
expect(r1).to_equal("ABCDEFG")
val r2 = to_text("HIJKLM")
expect(r2).to_equal("HIJKLM")
```

</details>

#### exercises uppercase N-Z in identifiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = to_text("NOPQR")
expect(r1).to_equal("NOPQR")
val r2 = to_text("STUVWXYZ")
expect(r2).to_equal("STUVWXYZ")
```

</details>

#### exercises underscore in identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Underscore is alpha in math tokenizer; tokenizes as single ident
val result = to_text("a_b")
expect(result).to_contain("a")
```

</details>

#### _can_start_expr and _can_implicit_mul edge cases

#### no implicit mul after operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After +, next token is num - not implicit mul context
val result = to_debug("a + 2")
expect(result).to_equal("Add(Id(a), Num(2))")
```

</details>

#### implicit mul with num before lparen

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("3(a + b)")
expect(result).to_contain("Mul")
expect(result).to_contain("Group")
```

</details>

#### tokenizer number-dot boundary

#### handles number followed by dot-dot range

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# In sum(i, 1..10), the 1 must not consume ".." as decimal
val result = to_debug("sum(i, 1..10) i")
expect(result).to_contain("Sum")
expect(result).to_contain("Num(1)")
expect(result).to_contain("Num(10)")
```

</details>

#### greek letter resolution through pretty renderer

#### resolves beta through pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("beta")).to_contain("\u03B2")
```

</details>

#### resolves gamma delta epsilon through pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("gamma")).to_contain("\u03B3")
expect(to_pretty("delta")).to_contain("\u03B4")
expect(to_pretty("epsilon")).to_contain("\u03B5")
```

</details>

#### resolves zeta eta theta through pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("zeta")).to_contain("\u03B6")
expect(to_pretty("eta")).to_contain("\u03B7")
expect(to_pretty("theta")).to_contain("\u03B8")
```

</details>

#### resolves iota kappa lambda through pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("iota")).to_contain("\u03B9")
expect(to_pretty("kappa")).to_contain("\u03BA")
expect(to_pretty("lambda")).to_contain("\u03BB")
```

</details>

#### resolves mu nu xi through pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("mu")).to_contain("\u03BC")
expect(to_pretty("nu")).to_contain("\u03BD")
expect(to_pretty("xi")).to_contain("\u03BE")
```

</details>

#### resolves omicron pi rho through pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("omicron")).to_contain("\u03BF")
expect(to_pretty("pi")).to_contain("\u03C0")
expect(to_pretty("rho")).to_contain("\u03C1")
```

</details>

#### resolves sigma tau upsilon through pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("sigma")).to_contain("\u03C3")
expect(to_pretty("tau")).to_contain("\u03C4")
expect(to_pretty("upsilon")).to_contain("\u03C5")
```

</details>

#### resolves phi chi psi omega through pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("phi")).to_contain("\u03C6")
expect(to_pretty("chi")).to_contain("\u03C7")
expect(to_pretty("psi")).to_contain("\u03C8")
expect(to_pretty("omega")).to_contain("\u03C9")
```

</details>

#### resolves variant forms through pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("varepsilon")).to_contain("\u03F5")
expect(to_pretty("vartheta")).to_contain("\u03D1")
expect(to_pretty("varphi")).to_contain("\u03D5")
expect(to_pretty("varrho")).to_contain("\u03F1")
```

</details>

#### resolves more variants and specials through pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("varpi")).to_contain("\u03D6")
expect(to_pretty("varkappa")).to_contain("\u03F0")
expect(to_pretty("partial")).to_contain("\u2202")
expect(to_pretty("nabla")).to_contain("\u2207")
```

</details>

#### uppercase greek through pretty renderer

#### resolves Delta Theta Lambda Xi through pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("Delta")).to_contain("\u0394")
expect(to_pretty("Theta")).to_contain("\u0398")
expect(to_pretty("Lambda")).to_contain("\u039B")
expect(to_pretty("Xi")).to_contain("\u039E")
```

</details>

#### resolves Pi Sigma Upsilon through pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("Pi")).to_contain("\u03A0")
expect(to_pretty("Sigma")).to_contain("\u03A3")
expect(to_pretty("Upsilon")).to_contain("\u03A5")
```

</details>

#### resolves Phi Psi Omega through pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("Phi")).to_contain("\u03A6")
expect(to_pretty("Psi")).to_contain("\u03A8")
expect(to_pretty("Omega")).to_contain("\u03A9")
```

</details>

#### greek through latex renderer

#### renders greek letters as latex commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_latex_raw("alpha")).to_contain("\\alpha")
expect(render_latex_raw("beta")).to_contain("\\beta")
expect(render_latex_raw("gamma")).to_contain("\\gamma")
```

</details>

#### renders uppercase greek as latex commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_latex_raw("Gamma")).to_contain("\\Gamma")
expect(render_latex_raw("Delta")).to_contain("\\Delta")
expect(render_latex_raw("Omega")).to_contain("\\Omega")
```

</details>

#### superscript char coverage through pretty power

#### exercises superscript digits 0-4 via power

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rn = to_pretty("x^n")
expect(rn).to_contain("x")
val ri = to_pretty("x^i")
expect(ri).to_contain("x")
```

</details>

#### subscript char coverage through pretty subscript

#### exercises subscript digits 0-4

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ra = to_pretty("x[a]")
expect(ra).to_contain("x")
val re = to_pretty("x[e]")
expect(re).to_contain("x")
val ro = to_pretty("x[o]")
expect(ro).to_contain("x")
```

</details>

#### exercises subscript letters h k l m n p s t

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ri = to_pretty("x[j]")
expect(ri).to_contain("x")
val rr = to_pretty("x[r]")
expect(rr).to_contain("x")
```

</details>

### math_repr empty input fallbacks

#### empty string fallback for each API function

#### to_debug handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("")
expect(result).to_contain("?")
```

</details>

#### to_pretty handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("")
expect(result).to_contain("?")
```

</details>

#### to_md handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_md("")
expect(result).to_start_with("$")
```

</details>

#### render_latex_raw handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
