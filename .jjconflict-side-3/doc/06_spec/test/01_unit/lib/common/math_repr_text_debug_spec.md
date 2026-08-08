# Math Repr Text and Debug Rendering

> Tests for to_text and to_debug renderers across all AST node types.

<!-- sdn-diagram:id=math_repr_text_debug_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_repr_text_debug_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_repr_text_debug_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_repr_text_debug_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/lib/common/math_repr_text_debug_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for to_text and to_debug renderers across all AST node types.

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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
