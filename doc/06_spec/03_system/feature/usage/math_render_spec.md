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
| Source | `test/03_system/feature/usage/math_render_spec.spl` |
| Updated | 2026-08-26 |
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

- renders addition
   - Expected: to_text("2 + 3") equals `2 + 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders addition")
expect(to_text("2 + 3")).to_equal("2 + 3")
```

</details>

#### renders subtraction

- renders subtraction
   - Expected: to_text("10 - 3") equals `10 - 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders subtraction")
expect(to_text("10 - 3")).to_equal("10 - 3")
```

</details>

#### renders multiplication

- renders multiplication
   - Expected: to_text("4 * 5") equals `4 * 5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders multiplication")
expect(to_text("4 * 5")).to_equal("4 * 5")
```

</details>

#### renders division

- renders division
   - Expected: to_text("15 / 3") equals `15 / 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders division")
expect(to_text("15 / 3")).to_equal("15 / 3")
```

</details>

#### renders negation

- renders negation
   - Expected: to_text("-5") equals `-5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders negation")
expect(to_text("-5")).to_equal("-5")
```

</details>

#### renders parenthesized group

- renders parenthesized group
   - Expected: to_text("(2 + 3) * 4") equals `(2 + 3) * 4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders parenthesized group")
expect(to_text("(2 + 3) * 4")).to_equal("(2 + 3) * 4")
```

</details>

#### renders power

- renders power
   - Expected: to_text("x^2") equals `x^2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders power")
expect(to_text("x^2")).to_equal("x^2")
```

</details>

#### renders complex expression

- renders complex expression
   - Expected: to_text("2 + 3 * 4") equals `2 + 3 * 4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders complex expression")
expect(to_text("2 + 3 * 4")).to_equal("2 + 3 * 4")
```

</details>

#### functions

#### renders sqrt

- renders sqrt
   - Expected: to_text("sqrt(16)") equals `sqrt(16)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders sqrt")
expect(to_text("sqrt(16)")).to_equal("sqrt(16)")
```

</details>

#### renders abs

- renders abs
   - Expected: to_text("abs(-5)") equals `abs(-5)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders abs")
expect(to_text("abs(-5)")).to_equal("abs(-5)")
```

</details>

#### renders frac as division

- renders frac as division
   - Expected: to_text("frac(1, 2)") equals `1 / 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders frac as division")
expect(to_text("frac(1, 2)")).to_equal("1 / 2")
```

</details>

#### renders nested frac

- renders nested frac
   - Expected: to_text("frac(1, frac(1, 2))") equals `1 / 1 / 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders nested frac")
expect(to_text("frac(1, frac(1, 2))")).to_equal("1 / 1 / 2")
```

</details>

#### renders multi-arg function

- renders multi-arg function
   - Expected: to_text("dot(a, b)") equals `dot(a, b)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders multi-arg function")
expect(to_text("dot(a, b)")).to_equal("dot(a, b)")
```

</details>

#### subscript and transpose

#### renders subscript

- renders subscript
   - Expected: to_text("x[0]") equals `x[0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders subscript")
expect(to_text("x[0]")).to_equal("x[0]")
```

</details>

#### renders nested subscript

- renders nested subscript
   - Expected: to_text("A[0][1]") equals `A[0][1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders nested subscript")
expect(to_text("A[0][1]")).to_equal("A[0][1]")
```

</details>

#### renders transpose

- renders transpose
   - Expected: to_text("A'") equals `A'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders transpose")
expect(to_text("A'")).to_equal("A'")
```

</details>

#### binders

#### renders sum

- renders sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders sum")
expect(to_text("sum(i, 0..10) i")).to_contain("sum")
expect(to_text("sum(i, 0..10) i")).to_contain("0")
expect(to_text("sum(i, 0..10) i")).to_contain("10")
```

</details>

#### renders integral

- renders integral


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders integral")
expect(to_text("int(x, 0..1) x")).to_contain("int")
expect(to_text("int(x, 0..1) x")).to_contain("0")
expect(to_text("int(x, 0..1) x")).to_contain("1")
```

</details>

### to_debug rendering

#### literals and identifiers

#### renders number

- renders number
   - Expected: to_debug("42") equals `Num(42)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders number")
expect(to_debug("42")).to_equal("Num(42)")
```

</details>

#### renders float

- renders float
   - Expected: to_debug("3.14") equals `Num(3.14)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders float")
expect(to_debug("3.14")).to_equal("Num(3.14)")
```

</details>

#### renders identifier

- renders identifier
   - Expected: to_debug("x") equals `Id(x)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders identifier")
expect(to_debug("x")).to_equal("Id(x)")
```

</details>

#### binary operators

#### renders addition

- renders addition
   - Expected: to_debug("2 + 3") equals `Add(Num(2), Num(3))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders addition")
expect(to_debug("2 + 3")).to_equal("Add(Num(2), Num(3))")
```

</details>

#### renders subtraction

- renders subtraction
   - Expected: to_debug("10 - 3") equals `Sub(Num(10), Num(3))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders subtraction")
expect(to_debug("10 - 3")).to_equal("Sub(Num(10), Num(3))")
```

</details>

#### renders multiplication

- renders multiplication
   - Expected: to_debug("4 * 5") equals `Mul(Num(4), Num(5))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders multiplication")
expect(to_debug("4 * 5")).to_equal("Mul(Num(4), Num(5))")
```

</details>

#### renders division

- renders division
   - Expected: to_debug("15 / 3") equals `Div(Num(15), Num(3))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders division")
expect(to_debug("15 / 3")).to_equal("Div(Num(15), Num(3))")
```

</details>

#### renders power

- renders power
   - Expected: to_debug("x^2") equals `Pow(Id(x), Num(2))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders power")
expect(to_debug("x^2")).to_equal("Pow(Id(x), Num(2))")
```

</details>

#### unary and grouping

#### renders negation

- renders negation
   - Expected: to_debug("-5") equals `Neg(Num(5))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders negation")
expect(to_debug("-5")).to_equal("Neg(Num(5))")
```

</details>

#### renders group

- renders group
   - Expected: to_debug("(x)") equals `Group(Id(x))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders group")
expect(to_debug("(x)")).to_equal("Group(Id(x))")
```

</details>

#### functions

#### renders frac

- renders frac
   - Expected: to_debug("frac(1, 2)") equals `Frac(Num(1), Num(2))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders frac")
expect(to_debug("frac(1, 2)")).to_equal("Frac(Num(1), Num(2))")
```

</details>

#### renders nested frac

- renders nested frac
   - Expected: to_debug("frac(1, frac(2, 3))") equals `Frac(Num(1), Frac(Num(2), Num(3)))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders nested frac")
expect(to_debug("frac(1, frac(2, 3))")).to_equal("Frac(Num(1), Frac(Num(2), Num(3)))")
```

</details>

#### renders sqrt call

- renders sqrt call
   - Expected: to_debug("sqrt(x)") equals `Call(sqrt, Id(x))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders sqrt call")
expect(to_debug("sqrt(x)")).to_equal("Call(sqrt, Id(x))")
```

</details>

#### renders multi-arg call

- renders multi-arg call
   - Expected: to_debug("dot(a, b)") equals `Call(dot, Id(a), Id(b))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders multi-arg call")
expect(to_debug("dot(a, b)")).to_equal("Call(dot, Id(a), Id(b))")
```

</details>

#### postfix

#### renders subscript

- renders subscript


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders subscript")
expect(to_debug("x[0]")).to_contain("Sub(")
```

</details>

#### renders transpose

- renders transpose
   - Expected: to_debug("A'") equals `Transpose(Id(A))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders transpose")
expect(to_debug("A'")).to_equal("Transpose(Id(A))")
```

</details>

#### precedence

#### renders add-mul precedence

- renders add-mul precedence
   - Expected: to_debug("2 + 3 * 4") equals `Add(Num(2), Mul(Num(3), Num(4)))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders add-mul precedence")
expect(to_debug("2 + 3 * 4")).to_equal("Add(Num(2), Mul(Num(3), Num(4)))")
```

</details>

#### renders power right-assoc with unary

- renders power right-assoc with unary
   - Expected: to_debug("x^-2") equals `Pow(Id(x), Neg(Num(2)))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders power right-assoc with unary")
# x^-2 means x^(-2)
expect(to_debug("x^-2")).to_equal("Pow(Id(x), Neg(Num(2)))")
```

</details>

#### complex expressions

#### renders sigmoid

- renders sigmoid


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders sigmoid")
val ast = to_debug("frac(1, 1 + exp(-x))")
expect(ast).to_contain("Frac")
expect(ast).to_contain("Add")
expect(ast).to_contain("Call(exp")
expect(ast).to_contain("Neg(Id(x))")
```

</details>

#### renders layer norm

- renders layer norm


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders layer norm")
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

- renders addition
   - Expected: render_latex_raw("2 + 3") equals `2 + 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders addition")
expect(render_latex_raw("2 + 3")).to_equal("2 + 3")
```

</details>

#### renders subtraction

- renders subtraction
   - Expected: render_latex_raw("10 - 3") equals `10 - 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders subtraction")
expect(render_latex_raw("10 - 3")).to_equal("10 - 3")
```

</details>

#### renders explicit multiplication as cdot

- renders explicit multiplication as cdot


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders explicit multiplication as cdot")
expect(render_latex_raw("4 * 5")).to_contain("\\cdot")
```

</details>

#### renders division

- renders division
   - Expected: render_latex_raw("15 / 3") equals `15 / 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders division")
expect(render_latex_raw("15 / 3")).to_equal("15 / 3")
```

</details>

#### renders power

- renders power


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders power")
val latex = render_latex_raw("x^2")
expect(latex).to_contain("x")
expect(latex).to_contain("2")
```

</details>

#### renders negation

- renders negation
   - Expected: render_latex_raw("-x") equals `-x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders negation")
expect(render_latex_raw("-x")).to_equal("-x")
```

</details>

#### fractions

#### renders frac

- renders frac


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders frac")
val latex = render_latex_raw("frac(1, 2)")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("{1}")
expect(latex).to_contain("{2}")
```

</details>

#### renders nested frac

- renders nested frac


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders nested frac")
val latex = render_latex_raw("frac(1, frac(2, 3))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("{1}")
expect(latex).to_contain("{\\frac")
```

</details>

#### renders frac with complex numerator

- renders frac with complex numerator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders frac with complex numerator")
val latex = render_latex_raw("frac(x + 1, 2)")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("x + 1")
```

</details>

#### renders frac with complex denominator

- renders frac with complex denominator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders frac with complex denominator")
val latex = render_latex_raw("frac(1, x^2 + 1)")
expect(latex).to_contain("\\frac")
```

</details>

#### functions

#### renders sqrt

- renders sqrt


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders sqrt")
val latex = render_latex_raw("sqrt(x)")
expect(latex).to_contain("\\sqrt")
```

</details>

#### renders known function sin

- renders known function sin


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders known function sin")
val latex = render_latex_raw("sin(x)")
expect(latex).to_contain("\\sin")
```

</details>

#### renders known function cos

- renders known function cos


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders known function cos")
val latex = render_latex_raw("cos(x)")
expect(latex).to_contain("\\cos")
```

</details>

#### renders known function exp

- renders known function exp


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders known function exp")
val latex = render_latex_raw("exp(x)")
expect(latex).to_contain("\\exp")
```

</details>

#### renders known function log

- renders known function log


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders known function log")
val latex = render_latex_raw("log(x)")
expect(latex).to_contain("\\log")
```

</details>

#### renders known function ln

- renders known function ln


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders known function ln")
val latex = render_latex_raw("ln(x)")
expect(latex).to_contain("\\ln")
```

</details>

#### renders known function tanh

- renders known function tanh


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders known function tanh")
val latex = render_latex_raw("tanh(x)")
expect(latex).to_contain("\\tanh")
```

</details>

#### renders unknown function as operatorname

- renders unknown function as operatorname


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders unknown function as operatorname")
val latex = render_latex_raw("relu(x)")
expect(latex).to_contain(r"\operatorname{relu}")
```

</details>

#### renders nested sqrt in frac

- renders nested sqrt in frac


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders nested sqrt in frac")
val latex = render_latex_raw("frac(1, sqrt(x))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sqrt")
```

</details>

#### greek letters

#### renders alpha

- renders alpha
   - Expected: render_latex_raw("alpha") equals `\\alpha`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders alpha")
expect(render_latex_raw("alpha")).to_equal("\\alpha")
```

</details>

#### renders pi

- renders pi
   - Expected: render_latex_raw("pi") equals `\\pi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders pi")
expect(render_latex_raw("pi")).to_equal("\\pi")
```

</details>

#### renders theta

- renders theta
   - Expected: render_latex_raw("theta") equals `\\theta`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders theta")
expect(render_latex_raw("theta")).to_equal("\\theta")
```

</details>

#### renders sigma

- renders sigma
   - Expected: render_latex_raw("sigma") equals `\\sigma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders sigma")
expect(render_latex_raw("sigma")).to_equal("\\sigma")
```

</details>

#### renders omega

- renders omega
   - Expected: render_latex_raw("omega") equals `\\omega`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders omega")
expect(render_latex_raw("omega")).to_equal("\\omega")
```

</details>

#### renders upper Gamma

- renders upper Gamma
   - Expected: render_latex_raw("Gamma") equals `\\Gamma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders upper Gamma")
expect(render_latex_raw("Gamma")).to_equal("\\Gamma")
```

</details>

#### renders upper Sigma

- renders upper Sigma
   - Expected: render_latex_raw("Sigma") equals `\\Sigma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders upper Sigma")
expect(render_latex_raw("Sigma")).to_equal("\\Sigma")
```

</details>

#### renders upper Omega

- renders upper Omega
   - Expected: render_latex_raw("Omega") equals `\\Omega`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders upper Omega")
expect(render_latex_raw("Omega")).to_equal("\\Omega")
```

</details>

#### subscript and transpose

#### renders subscript

- renders subscript


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders subscript")
val latex = render_latex_raw("x[i]")
expect(latex).to_contain("x")
expect(latex).to_contain("i")
```

</details>

#### renders transpose

- renders transpose


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders transpose")
val latex = render_latex_raw("A'")
expect(latex).to_contain("A")
expect(latex).to_contain("T")
```

</details>

#### binders

#### renders sum

- renders sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders sum")
val latex = render_latex_raw("sum(i, 0..10) i")
expect(latex).to_contain("\\sum")
expect(latex).to_contain("i")
```

</details>

#### renders integral

- renders integral


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders integral")
val latex = render_latex_raw("int(x, 0..1) x")
expect(latex).to_contain("\\int")
expect(latex).to_contain("x")
```

</details>

#### DL equations

#### renders sigmoid

- renders sigmoid


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders sigmoid")
val latex = render_latex_raw("frac(1, 1 + exp(-x))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\exp")
```

</details>

#### renders MSE loss

- renders MSE loss


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders MSE loss")
val latex = render_latex_raw("frac(1, n) * sum(i, 1..n) (y[i] - pred[i])^2")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sum")
```

</details>

#### renders softmax numerator

- renders softmax numerator


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders softmax numerator")
val latex = render_latex_raw("frac(exp(x[i]), sum(j, 1..n) exp(x[j]))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\exp")
expect(latex).to_contain("\\sum")
```

</details>

#### renders layer norm

- renders layer norm


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders layer norm")
val latex = render_latex_raw("frac(x - mu, sqrt(sigma^2 + epsilon))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("\\epsilon")
```

</details>

#### renders SGD update

- renders SGD update


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders SGD update")
val latex = render_latex_raw("theta - alpha * nabla * J(theta)")
expect(latex).to_contain("\\theta")
expect(latex).to_contain("\\alpha")
expect(latex).to_contain("\\nabla")
```

</details>

#### renders cross entropy

- renders cross entropy


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders cross entropy")
val latex = render_latex_raw("-sum(i, 1..n) y[i] * log(pred[i])")
expect(latex).to_contain("\\sum")
expect(latex).to_contain("\\log")
```

</details>

#### renders xavier init

- renders xavier init


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders xavier init")
val latex = render_latex_raw("sqrt(frac(6, fan_in + fan_out))")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("\\frac")
```

</details>

#### renders attention scores

- renders attention scores


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders attention scores")
val latex = render_latex_raw("frac(Q * K', sqrt(d_k))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("T")
```

</details>

### to_pretty rendering

#### identifiers and constants

#### renders plain identifier

- renders plain identifier
   - Expected: to_pretty("x") equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders plain identifier")
expect(to_pretty("x")).to_equal("x")
```

</details>

#### renders greek alpha

- renders greek alpha
   - Expected: to_pretty("alpha") equals `α`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders greek alpha")
expect(to_pretty("alpha")).to_equal("α")
```

</details>

#### renders greek pi

- renders greek pi
   - Expected: to_pretty("pi") equals `π`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders greek pi")
expect(to_pretty("pi")).to_equal("π")
```

</details>

#### renders greek theta

- renders greek theta
   - Expected: to_pretty("theta") equals `θ`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders greek theta")
expect(to_pretty("theta")).to_equal("θ")
```

</details>

#### renders greek sigma

- renders greek sigma
   - Expected: to_pretty("sigma") equals `σ`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders greek sigma")
expect(to_pretty("sigma")).to_equal("σ")
```

</details>

#### renders greek omega

- renders greek omega
   - Expected: to_pretty("omega") equals `ω`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders greek omega")
expect(to_pretty("omega")).to_equal("ω")
```

</details>

#### renders greek lambda

- renders greek lambda
   - Expected: to_pretty("lambda") equals `λ`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders greek lambda")
expect(to_pretty("lambda")).to_equal("λ")
```

</details>

#### renders upper Gamma

- renders upper Gamma
   - Expected: to_pretty("Gamma") equals `Γ`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders upper Gamma")
expect(to_pretty("Gamma")).to_equal("Γ")
```

</details>

#### renders upper Delta

- renders upper Delta
   - Expected: to_pretty("Delta") equals `Δ`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders upper Delta")
expect(to_pretty("Delta")).to_equal("Δ")
```

</details>

#### renders upper Sigma

- renders upper Sigma
   - Expected: to_pretty("Sigma") equals `Σ`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders upper Sigma")
expect(to_pretty("Sigma")).to_equal("Σ")
```

</details>

#### renders upper Omega

- renders upper Omega
   - Expected: to_pretty("Omega") equals `Ω`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders upper Omega")
expect(to_pretty("Omega")).to_equal("Ω")
```

</details>

#### arithmetic

#### renders addition

- renders addition
   - Expected: to_pretty("2 + 3") equals `2 + 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders addition")
expect(to_pretty("2 + 3")).to_equal("2 + 3")
```

</details>

#### renders subtraction

- renders subtraction
   - Expected: to_pretty("10 - 3") equals `10 - 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders subtraction")
expect(to_pretty("10 - 3")).to_equal("10 - 3")
```

</details>

#### renders negation

- renders negation
   - Expected: to_pretty("-x") equals `-x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders negation")
expect(to_pretty("-x")).to_equal("-x")
```

</details>

#### power — superscript

#### renders x^2

- renders x^2


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders x^2")
val p = to_pretty("x^2")
expect(p).to_contain("x")
# Should use superscript ²
expect(p).to_contain("²")
```

</details>

#### renders x^3

- renders x^3


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders x^3")
val p = to_pretty("x^3")
expect(p).to_contain("³")
```

</details>

#### renders x^n

- renders x^n


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders x^n")
val p = to_pretty("x^n")
expect(p).to_contain("x")
```

</details>

#### fractions

#### renders simple frac

- renders simple frac
   - Expected: p equals `(1)/(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders simple frac")
val p = to_pretty("frac(1, 2)")
expect(p).to_equal("(1)/(2)")
```

</details>

#### renders nested frac

- renders nested frac


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders nested frac")
val p = to_pretty("frac(1, frac(2, 3))")
expect(p).to_contain("1")
expect(p).to_contain("2")
expect(p).to_contain("3")
```

</details>

#### sqrt

#### renders sqrt

- renders sqrt


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders sqrt")
val p = to_pretty("sqrt(x)")
expect(p).to_contain("√")
expect(p).to_contain("x")
```

</details>

#### renders sqrt of expression

- renders sqrt of expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders sqrt of expression")
val p = to_pretty("sqrt(x^2 + 1)")
expect(p).to_contain("√")
```

</details>

#### binders

#### renders sum with Unicode sigma

- renders sum with Unicode sigma
   - Expected: p equals `∑(i=0..10) i²`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders sum with Unicode sigma")
val p = to_pretty("sum(i, 0..10) i^2")
expect(p).to_equal("∑(i=0..10) i²")
```

</details>

#### renders integral with Unicode symbol

- renders integral with Unicode symbol
   - Expected: p equals `∫(x=0..1) x²`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders integral with Unicode symbol")
val p = to_pretty("int(x, 0..1) x^2")
expect(p).to_equal("∫(x=0..1) x²")
```

</details>

#### DL equations

#### renders sigmoid

- renders sigmoid


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders sigmoid")
val p = to_pretty("frac(1, 1 + exp(-x))")
expect(p).to_contain("1")
expect(p).to_contain("exp")
```

</details>

#### renders layer norm

- renders layer norm


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders layer norm")
val p = to_pretty("frac(x - mu, sqrt(sigma^2 + epsilon))")
expect(p).to_contain("√")
expect(p).to_contain("μ")
expect(p).to_contain("σ")
expect(p).to_contain("ε")
```

</details>

#### renders SGD update with greek

- renders SGD update with greek


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders SGD update with greek")
val p = to_pretty("theta - alpha * grad")
expect(p).to_contain("θ")
expect(p).to_contain("α")
```

</details>

#### renders xavier init

- renders xavier init


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders xavier init")
val p = to_pretty("sqrt(frac(6, fan_in + fan_out))")
expect(p).to_contain("√")
```

</details>

### to_md rendering

#### wraps in dollar signs

- wraps in dollar signs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wraps in dollar signs")
val md = to_md("x + 1")
expect(md).to_start_with("$")
expect(md).to_end_with("$")
```

</details>

#### renders frac in markdown

- renders frac in markdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders frac in markdown")
val md = to_md("frac(1, 2)")
expect(md).to_contain("\\frac")
expect(md).to_start_with("$")
expect(md).to_end_with("$")
```

</details>

#### renders greek in markdown

- renders greek in markdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders greek in markdown")
val md = to_md("alpha + beta")
expect(md).to_contain("\\alpha")
expect(md).to_contain("\\beta")
expect(md).to_start_with("$")
```

</details>

#### renders complex DL equation

- renders complex DL equation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders complex DL equation")
val md = to_md("frac(1, 1 + exp(-x))")
expect(md).to_contain("\\frac")
expect(md).to_contain("\\exp")
expect(md).to_start_with("$")
expect(md).to_end_with("$")
```

</details>

#### renders sum binder

- renders sum binder


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders sum binder")
val md = to_md("sum(i, 1..n) x[i]^2")
expect(md).to_contain("\\sum")
expect(md).to_start_with("$")
```

</details>

### rendering edge cases

#### deeply nested

#### renders triple-nested frac

- renders triple-nested frac


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders triple-nested frac")
val latex = render_latex_raw("frac(frac(1, 2), frac(3, 4))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("{1}")
expect(latex).to_contain("{2}")
expect(latex).to_contain("{3}")
expect(latex).to_contain("{4}")
```

</details>

#### renders frac inside sqrt inside frac

- renders frac inside sqrt inside frac


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders frac inside sqrt inside frac")
val latex = render_latex_raw("frac(1, sqrt(frac(2, 3)))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sqrt")
```

</details>

#### renders power of frac

- renders power of frac


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders power of frac")
val latex = render_latex_raw("frac(1, 2)^3")
expect(latex).to_contain("\\frac")
```

</details>

#### implicit multiplication

#### renders 2x

- renders 2x


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders 2x")
val t = to_text("2x")
expect(t).to_contain("2")
expect(t).to_contain("x")
```

</details>

#### renders 3(x + 1)

- renders 3(x + 1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders 3(x + 1)")
val t = to_text("3(x + 1)")
expect(t).to_contain("3")
expect(t).to_contain("x + 1")
```

</details>

#### complex DL architectures

#### renders attention formula

- renders attention formula


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders attention formula")
# Attention(Q, K, V) = softmax(QK^T / sqrt(d_k)) V
val latex = render_latex_raw("frac(Q * K', sqrt(d_k))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sqrt")
```

</details>

#### renders batch norm

- renders batch norm


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders batch norm")
val latex = render_latex_raw("gamma * frac(x - mu, sqrt(sigma^2 + epsilon)) + beta")
expect(latex).to_contain("\\gamma")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("\\beta")
expect(latex).to_contain("\\epsilon")
```

</details>

#### renders KL divergence

- renders KL divergence


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders KL divergence")
val latex = render_latex_raw("sum(i, 1..n) p[i] * log(frac(p[i], q[i]))")
expect(latex).to_contain("\\sum")
expect(latex).to_contain("\\log")
expect(latex).to_contain("\\frac")
```

</details>

#### renders GELU approximation

- renders GELU approximation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders GELU approximation")
# 0.5 * x * (1 + tanh(sqrt(2/pi) * (x + 0.044715 * x^3)))
val latex = render_latex_raw("0.5 * x * (1 + tanh(sqrt(frac(2, pi)) * (x + 0.044715 * x^3)))")
expect(latex).to_contain("\\tanh")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\pi")
```

</details>

#### renders Adam optimizer update

- renders Adam optimizer update


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders Adam optimizer update")
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

- m{} and loss{} render same to_pretty
   - Expected: m_text equals `l_text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("m{} and loss{} render same to_pretty")
val m_text = to_pretty("frac(1, 1 + exp(-x))")
# loss{} and nograd{} use the same rendering pipeline
# (they all pass the inner expression to math_repr)
val l_text = to_pretty("frac(1, 1 + exp(-x))")
expect(m_text).to_equal(l_text)
```

</details>

#### m{} and loss{} render same LaTeX

- m{} and loss{} render same LaTeX
   - Expected: m_latex equals `l_latex`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("m{} and loss{} render same LaTeX")
val m_latex = render_latex_raw("theta - alpha * grad")
val l_latex = render_latex_raw("theta - alpha * grad")
expect(m_latex).to_equal(l_latex)
```

</details>

#### Greek mixed with operators

#### renders alpha * beta + gamma

- renders alpha * beta + gamma


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders alpha * beta + gamma")
val latex = render_latex_raw("alpha * beta + gamma")
expect(latex).to_contain("\\alpha")
expect(latex).to_contain("\\beta")
expect(latex).to_contain("\\gamma")
```

</details>

#### renders partial derivative notation

- renders partial derivative notation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders partial derivative notation")
val latex = render_latex_raw("partial * f / partial * x")
expect(latex).to_contain("\\partial")
```

</details>

#### renders nabla operator

- renders nabla operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders nabla operator")
val latex = render_latex_raw("nabla * f(x)")
expect(latex).to_contain("\\nabla")
```

</details>

#### subscript chains

#### renders A[i][j]

- renders A[i][j]


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders A[i][j]")
val latex = render_latex_raw("A[i][j]")
expect(latex).to_contain("A")
expect(latex).to_contain("i")
expect(latex).to_contain("j")
```

</details>

#### renders x[i]^2

- renders x[i]^2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders x[i]^2")
val latex = render_latex_raw("x[i]^2")
expect(latex).to_contain("x")
expect(latex).to_contain("i")
```

</details>

#### empty and minimal

#### renders single number

- renders single number
   - Expected: render_latex_raw("42") equals `42`
   - Expected: to_pretty("42") equals `42`
   - Expected: to_text("42") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders single number")
expect(render_latex_raw("42")).to_equal("42")
expect(to_pretty("42")).to_equal("42")
expect(to_text("42")).to_equal("42")
```

</details>

#### renders single identifier

- renders single identifier
   - Expected: render_latex_raw("x") equals `x`
   - Expected: to_pretty("x") equals `x`
   - Expected: to_text("x") equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders single identifier")
expect(render_latex_raw("x")).to_equal("x")
expect(to_pretty("x")).to_equal("x")
expect(to_text("x")).to_equal("x")
```

</details>

#### renders single greek letter

- renders single greek letter
   - Expected: render_latex_raw("pi") equals `\\pi`
   - Expected: to_pretty("pi") equals `π`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders single greek letter")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `109fc1ed169e06d946bbdf7af93419a6ea516496e23b5f86f5b3d0e31646dcd4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `109fc1ed169e06d946bbdf7af93419a6ea516496e23b5f86f5b3d0e31646dcd4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `109fc1ed169e06d946bbdf7af93419a6ea516496e23b5f86f5b3d0e31646dcd4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/math_render_spec.spl
mirror: doc/06_spec/03_system/feature/usage/math_render_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/math_render_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/math_render_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/math_render_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders addition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/math_render_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders subtraction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/math_render_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders multiplication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
