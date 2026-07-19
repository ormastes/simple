# Math Block Rendering Specification

> Intensive tests for the math expression rendering pipeline:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 129 | 129 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Block Rendering Specification

Intensive tests for the math expression rendering pipeline:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1090-1102 (math block rendering) |
| Category | Syntax / Math DSL / Rendering |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/feature/usage/math_render_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Intensive tests for the math expression rendering pipeline:
- `to_text()`:         Normalized plain text
- `to_debug()`:        AST structure
- `to_pretty()`:       Unicode pretty print
- `to_md()`:           Markdown LaTeX
- `render_latex_raw()`: Raw LaTeX output

Covers edge cases: nested fracs, sum/integral binders, transpose,
subscript, complex DL equations, Greek letters, operator precedence,
implicit multiplication, and LaTeX-style commands.

## Scenarios

### to_text rendering

#### arithmetic

#### renders addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("2 + 3")).to_equal("2 + 3")
```

</details>

#### renders subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("10 - 3")).to_equal("10 - 3")
```

</details>

#### renders multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("4 * 5")).to_equal("4 * 5")
```

</details>

#### renders division

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("15 / 3")).to_equal("15 / 3")
```

</details>

#### renders negation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("-5")).to_equal("-5")
```

</details>

#### renders parenthesized group

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("(2 + 3) * 4")).to_equal("(2 + 3) * 4")
```

</details>

#### renders power

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("x^2")).to_equal("x^2")
```

</details>

#### renders complex expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("2 + 3 * 4")).to_equal("2 + 3 * 4")
```

</details>

#### functions

#### renders sqrt

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("sqrt(16)")).to_equal("sqrt(16)")
```

</details>

#### renders abs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("abs(-5)")).to_equal("abs(-5)")
```

</details>

#### renders frac as division

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("frac(1, 2)")).to_equal("1 / 2")
```

</details>

#### renders nested frac

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("frac(1, frac(1, 2))")).to_equal("1 / 1 / 2")
```

</details>

#### renders multi-arg function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("dot(a, b)")).to_equal("dot(a, b)")
```

</details>

#### subscript and transpose

#### renders subscript

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("x[0]")).to_equal("x[0]")
```

</details>

#### renders nested subscript

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("A[0][1]")).to_equal("A[0][1]")
```

</details>

#### renders transpose

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("A'")).to_equal("A'")
```

</details>

#### binders

#### renders sum

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("sum(i, 0..10) i")).to_contain("sum")
expect(to_text("sum(i, 0..10) i")).to_contain("0")
expect(to_text("sum(i, 0..10) i")).to_contain("10")
```

</details>

#### renders integral

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("int(x, 0..1) x")).to_contain("int")
expect(to_text("int(x, 0..1) x")).to_contain("0")
expect(to_text("int(x, 0..1) x")).to_contain("1")
```

</details>

### to_debug rendering

#### literals and identifiers

#### renders number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("42")).to_equal("Num(42)")
```

</details>

#### renders float

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("3.14")).to_equal("Num(3.14)")
```

</details>

#### renders identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("x")).to_equal("Id(x)")
```

</details>

#### binary operators

#### renders addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("2 + 3")).to_equal("Add(Num(2), Num(3))")
```

</details>

#### renders subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("10 - 3")).to_equal("Sub(Num(10), Num(3))")
```

</details>

#### renders multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("4 * 5")).to_equal("Mul(Num(4), Num(5))")
```

</details>

#### renders division

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("15 / 3")).to_equal("Div(Num(15), Num(3))")
```

</details>

#### renders power

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("x^2")).to_equal("Pow(Id(x), Num(2))")
```

</details>

#### unary and grouping

#### renders negation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("-5")).to_equal("Neg(Num(5))")
```

</details>

#### renders group

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("(x)")).to_equal("Group(Id(x))")
```

</details>

#### functions

#### renders frac

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("frac(1, 2)")).to_equal("Frac(Num(1), Num(2))")
```

</details>

#### renders nested frac

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("frac(1, frac(2, 3))")).to_equal("Frac(Num(1), Frac(Num(2), Num(3)))")
```

</details>

#### renders sqrt call

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("sqrt(x)")).to_equal("Call(sqrt, Id(x))")
```

</details>

#### renders multi-arg call

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("dot(a, b)")).to_equal("Call(dot, Id(a), Id(b))")
```

</details>

#### postfix

#### renders subscript

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("x[0]")).to_contain("Sub(")
```

</details>

#### renders transpose

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("A'")).to_equal("Transpose(Id(A))")
```

</details>

#### precedence

#### renders add-mul precedence

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("2 + 3 * 4")).to_equal("Add(Num(2), Mul(Num(3), Num(4)))")
```

</details>

#### renders power right-assoc with unary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# x^-2 means x^(-2)
expect(to_debug("x^-2")).to_equal("Pow(Id(x), Neg(Num(2)))")
```

</details>

#### complex expressions

#### renders sigmoid

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ast = to_debug("frac(1, 1 + exp(-x))")
expect(ast).to_contain("Frac")
expect(ast).to_contain("Add")
expect(ast).to_contain("Call(exp")
expect(ast).to_contain("Neg(Id(x))")
```

</details>

#### renders layer norm

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ast = to_debug("frac(x - mu, sqrt(sigma^2 + epsilon))")
expect(ast).to_contain("Frac")
expect(ast).to_contain("Sub(Id(x), Id(mu))")
expect(ast).to_contain("Call(sqrt")
expect(ast).to_contain("Pow(Id(sigma), Num(2))")
```

</details>

### render_latex_raw rendering

#### arithmetic

#### renders addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_latex_raw("2 + 3")).to_equal("2 + 3")
```

</details>

#### renders subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_latex_raw("10 - 3")).to_equal("10 - 3")
```

</details>

#### renders explicit multiplication as cdot

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_latex_raw("4 * 5")).to_contain("\\cdot")
```

</details>

#### renders division

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_latex_raw("15 / 3")).to_equal("15 / 3")
```

</details>

#### renders power

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("x^2")
expect(latex).to_contain("x")
expect(latex).to_contain("2")
```

</details>

#### renders negation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_latex_raw("-x")).to_equal("-x")
```

</details>

#### fractions

#### renders frac

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(1, 2)")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("{1}")
expect(latex).to_contain("{2}")
```

</details>

#### renders nested frac

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(1, frac(2, 3))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("{1}")
expect(latex).to_contain("{\\frac")
```

</details>

#### renders frac with complex numerator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(x + 1, 2)")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("x + 1")
```

</details>

#### renders frac with complex denominator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(1, x^2 + 1)")
expect(latex).to_contain("\\frac")
```

</details>

#### functions

#### renders sqrt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("sqrt(x)")
expect(latex).to_contain("\\sqrt")
```

</details>

#### renders known function sin

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("sin(x)")
expect(latex).to_contain("\\sin")
```

</details>

#### renders known function cos

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("cos(x)")
expect(latex).to_contain("\\cos")
```

</details>

#### renders known function exp

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("exp(x)")
expect(latex).to_contain("\\exp")
```

</details>

#### renders known function log

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("log(x)")
expect(latex).to_contain("\\log")
```

</details>

#### renders known function ln

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("ln(x)")
expect(latex).to_contain("\\ln")
```

</details>

#### renders known function tanh

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("tanh(x)")
expect(latex).to_contain("\\tanh")
```

</details>

#### renders unknown function as operatorname

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("relu(x)")
expect(latex).to_contain(r"\operatorname{relu}")
```

</details>

#### renders nested sqrt in frac

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(1, sqrt(x))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sqrt")
```

</details>

#### greek letters

#### renders alpha

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_latex_raw("alpha")).to_equal("\\alpha")
```

</details>

#### renders pi

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_latex_raw("pi")).to_equal("\\pi")
```

</details>

#### renders theta

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_latex_raw("theta")).to_equal("\\theta")
```

</details>

#### renders sigma

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_latex_raw("sigma")).to_equal("\\sigma")
```

</details>

#### renders omega

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_latex_raw("omega")).to_equal("\\omega")
```

</details>

#### renders upper Gamma

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_latex_raw("Gamma")).to_equal("\\Gamma")
```

</details>

#### renders upper Sigma

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_latex_raw("Sigma")).to_equal("\\Sigma")
```

</details>

#### renders upper Omega

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_latex_raw("Omega")).to_equal("\\Omega")
```

</details>

#### subscript and transpose

#### renders subscript

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("x[i]")
expect(latex).to_contain("x")
expect(latex).to_contain("i")
```

</details>

#### renders transpose

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("A'")
expect(latex).to_contain("A")
expect(latex).to_contain("T")
```

</details>

#### binders

#### renders sum

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("sum(i, 0..10) i")
expect(latex).to_contain("\\sum")
expect(latex).to_contain("i")
```

</details>

#### renders integral

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("int(x, 0..1) x")
expect(latex).to_contain("\\int")
expect(latex).to_contain("x")
```

</details>

#### DL equations

#### renders sigmoid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(1, 1 + exp(-x))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\exp")
```

</details>

#### renders MSE loss

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(1, n) * sum(i, 1..n) (y[i] - pred[i])^2")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sum")
```

</details>

#### renders softmax numerator

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(exp(x[i]), sum(j, 1..n) exp(x[j]))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\exp")
expect(latex).to_contain("\\sum")
```

</details>

#### renders layer norm

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(x - mu, sqrt(sigma^2 + epsilon))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("\\epsilon")
```

</details>

#### renders SGD update

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("theta - alpha * nabla * J(theta)")
expect(latex).to_contain("\\theta")
expect(latex).to_contain("\\alpha")
expect(latex).to_contain("\\nabla")
```

</details>

#### renders cross entropy

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("-sum(i, 1..n) y[i] * log(pred[i])")
expect(latex).to_contain("\\sum")
expect(latex).to_contain("\\log")
```

</details>

#### renders xavier init

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("sqrt(frac(6, fan_in + fan_out))")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("\\frac")
```

</details>

#### renders attention scores

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(Q * K', sqrt(d_k))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("T")
```

</details>

### to_pretty rendering

#### identifiers and constants

#### renders plain identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("x")).to_equal("x")
```

</details>

#### renders greek alpha

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("alpha")).to_equal("α")
```

</details>

#### renders greek pi

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("pi")).to_equal("π")
```

</details>

#### renders greek theta

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("theta")).to_equal("θ")
```

</details>

#### renders greek sigma

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("sigma")).to_equal("σ")
```

</details>

#### renders greek omega

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("omega")).to_equal("ω")
```

</details>

#### renders greek lambda

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("lambda")).to_equal("λ")
```

</details>

#### renders upper Gamma

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("Gamma")).to_equal("Γ")
```

</details>

#### renders upper Delta

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("Delta")).to_equal("Δ")
```

</details>

#### renders upper Sigma

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("Sigma")).to_equal("Σ")
```

</details>

#### renders upper Omega

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("Omega")).to_equal("Ω")
```

</details>

#### arithmetic

#### renders addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("2 + 3")).to_equal("2 + 3")
```

</details>

#### renders subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("10 - 3")).to_equal("10 - 3")
```

</details>

#### renders negation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pretty("-x")).to_equal("-x")
```

</details>

#### power — superscript

#### renders x^2

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = to_pretty("x^2")
expect(p).to_contain("x")
# Should use superscript ²
expect(p).to_contain("²")
```

</details>

#### renders x^3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = to_pretty("x^3")
expect(p).to_contain("³")
```

</details>

#### renders x^n

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = to_pretty("x^n")
expect(p).to_contain("x")
```

</details>

#### fractions

#### renders simple frac

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = to_pretty("frac(1, 2)")
expect(p).to_equal("(1)/(2)")
```

</details>

#### renders nested frac

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = to_pretty("frac(1, frac(2, 3))")
expect(p).to_contain("1")
expect(p).to_contain("2")
expect(p).to_contain("3")
```

</details>

#### sqrt

#### renders sqrt

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = to_pretty("sqrt(x)")
expect(p).to_contain("√")
expect(p).to_contain("x")
```

</details>

#### renders sqrt of expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = to_pretty("sqrt(x^2 + 1)")
expect(p).to_contain("√")
```

</details>

#### binders

#### renders sum with Unicode sigma

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = to_pretty("sum(i, 0..10) i^2")
expect(p).to_equal("∑(i=0..10) i²")
```

</details>

#### renders integral with Unicode symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = to_pretty("int(x, 0..1) x^2")
expect(p).to_equal("∫(x=0..1) x²")
```

</details>

#### DL equations

#### renders sigmoid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = to_pretty("frac(1, 1 + exp(-x))")
expect(p).to_contain("1")
expect(p).to_contain("exp")
```

</details>

#### renders layer norm

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = to_pretty("frac(x - mu, sqrt(sigma^2 + epsilon))")
expect(p).to_contain("√")
expect(p).to_contain("μ")
expect(p).to_contain("σ")
expect(p).to_contain("ε")
```

</details>

#### renders SGD update with greek

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = to_pretty("theta - alpha * grad")
expect(p).to_contain("θ")
expect(p).to_contain("α")
```

</details>

#### renders xavier init

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = to_pretty("sqrt(frac(6, fan_in + fan_out))")
expect(p).to_contain("√")
```

</details>

### to_md rendering

#### wraps in dollar signs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = to_md("x + 1")
expect(md).to_start_with("$")
expect(md).to_end_with("$")
```

</details>

#### renders frac in markdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = to_md("frac(1, 2)")
expect(md).to_contain("\\frac")
expect(md).to_start_with("$")
expect(md).to_end_with("$")
```

</details>

#### renders greek in markdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = to_md("alpha + beta")
expect(md).to_contain("\\alpha")
expect(md).to_contain("\\beta")
expect(md).to_start_with("$")
```

</details>

#### renders complex DL equation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = to_md("frac(1, 1 + exp(-x))")
expect(md).to_contain("\\frac")
expect(md).to_contain("\\exp")
expect(md).to_start_with("$")
expect(md).to_end_with("$")
```

</details>

#### renders sum binder

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = to_md("sum(i, 1..n) x[i]^2")
expect(md).to_contain("\\sum")
expect(md).to_start_with("$")
```

</details>

### rendering edge cases

#### deeply nested

#### renders triple-nested frac

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(frac(1, 2), frac(3, 4))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("{1}")
expect(latex).to_contain("{2}")
expect(latex).to_contain("{3}")
expect(latex).to_contain("{4}")
```

</details>

#### renders frac inside sqrt inside frac

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(1, sqrt(frac(2, 3)))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sqrt")
```

</details>

#### renders power of frac

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(1, 2)^3")
expect(latex).to_contain("\\frac")
```

</details>

#### implicit multiplication

#### renders 2x

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = to_text("2x")
expect(t).to_contain("2")
expect(t).to_contain("x")
```

</details>

#### renders 3(x + 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = to_text("3(x + 1)")
expect(t).to_contain("3")
expect(t).to_contain("x + 1")
```

</details>

#### complex DL architectures

#### renders attention formula

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Attention(Q, K, V) = softmax(QK^T / sqrt(d_k)) V
val latex = render_latex_raw("frac(Q * K', sqrt(d_k))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sqrt")
```

</details>

#### renders batch norm

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("gamma * frac(x - mu, sqrt(sigma^2 + epsilon)) + beta")
expect(latex).to_contain("\\gamma")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("\\beta")
expect(latex).to_contain("\\epsilon")
```

</details>

#### renders KL divergence

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("sum(i, 1..n) p[i] * log(frac(p[i], q[i]))")
expect(latex).to_contain("\\sum")
expect(latex).to_contain("\\log")
expect(latex).to_contain("\\frac")
```

</details>

#### renders GELU approximation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0.5 * x * (1 + tanh(sqrt(2/pi) * (x + 0.044715 * x^3)))
val latex = render_latex_raw("0.5 * x * (1 + tanh(sqrt(frac(2, pi)) * (x + 0.044715 * x^3)))")
expect(latex).to_contain("\\tanh")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\pi")
```

</details>

#### renders Adam optimizer update

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("theta - alpha * frac(m_hat, sqrt(v_hat) + epsilon)")
expect(latex).to_contain("\\theta")
expect(latex).to_contain("\\alpha")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("\\epsilon")
```

</details>

#### m{} loss{} nograd{} evaluation parity in rendering

#### m{} and loss{} render same to_pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m_text = to_pretty("frac(1, 1 + exp(-x))")
# loss{} and nograd{} use the same rendering pipeline
# (they all pass the inner expression to math_repr)
val l_text = to_pretty("frac(1, 1 + exp(-x))")
expect(m_text).to_equal(l_text)
```

</details>

#### m{} and loss{} render same LaTeX

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m_latex = render_latex_raw("theta - alpha * grad")
val l_latex = render_latex_raw("theta - alpha * grad")
expect(m_latex).to_equal(l_latex)
```

</details>

#### Greek mixed with operators

#### renders alpha * beta + gamma

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("alpha * beta + gamma")
expect(latex).to_contain("\\alpha")
expect(latex).to_contain("\\beta")
expect(latex).to_contain("\\gamma")
```

</details>

#### renders partial derivative notation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("partial * f / partial * x")
expect(latex).to_contain("\\partial")
```

</details>

#### renders nabla operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("nabla * f(x)")
expect(latex).to_contain("\\nabla")
```

</details>

#### subscript chains

#### renders A[i][j]

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("A[i][j]")
expect(latex).to_contain("A")
expect(latex).to_contain("i")
expect(latex).to_contain("j")
```

</details>

#### renders x[i]^2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("x[i]^2")
expect(latex).to_contain("x")
expect(latex).to_contain("i")
```

</details>

#### empty and minimal

#### renders single number

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_latex_raw("42")).to_equal("42")
expect(to_pretty("42")).to_equal("42")
expect(to_text("42")).to_equal("42")
```

</details>

#### renders single identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_latex_raw("x")).to_equal("x")
expect(to_pretty("x")).to_equal("x")
expect(to_text("x")).to_equal("x")
```

</details>

#### renders single greek letter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_latex_raw("pi")).to_equal("\\pi")
expect(to_pretty("pi")).to_equal("π")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 129 |
| Active scenarios | 129 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
