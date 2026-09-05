# Math Repr Pretty, LaTeX, and Renderer Symbols

> Tests for to_pretty, to_md, render_latex_raw, empty fallbacks, int_expr paths, renderer edge cases, superscript/subscript chars, and greek symbols.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 105 | 105 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Repr Pretty, LaTeX, and Renderer Symbols

Tests for to_pretty, to_md, render_latex_raw, empty fallbacks, int_expr paths, renderer edge cases, superscript/subscript chars, and greek symbols.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-MATH-COV |
| Category | Stdlib |
| Status | Implemented |
| Source | `test/01_unit/lib/common/math_repr_pretty_latex_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for to_pretty, to_md, render_latex_raw, empty fallbacks,
int_expr paths, renderer edge cases, superscript/subscript chars, and greek symbols.

## Scenarios

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

#### renders transpose with Unicode T suffix

- renders transpose with Unicode T suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders transpose with Unicode T suffix")
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

### math_repr int_expr all renderers

#### integral through text renderer

#### renders integral via to_text

- renders integral via to_text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders integral via to_text")
val result = to_text("int(t, 0..1) t")
expect(result).to_contain("int")
expect(result).to_contain("t")
```

</details>

#### integral through debug renderer

#### renders integral via to_debug

- renders integral via to_debug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders integral via to_debug")
val result = to_debug("int(t, 0..1) t")
expect(result).to_contain("Int")
```

</details>

#### integral through pretty renderer

#### renders integral via to_pretty

- renders integral via to_pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders integral via to_pretty")
val result = to_pretty("int(t, 0..1) t")
expect(result).to_contain("t")
```

</details>

#### integral through latex renderer

#### renders integral via render_latex_raw

- renders integral via render_latex_raw


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders integral via render_latex_raw")
val result = render_latex_raw("int(t, 0..1) t")
expect(result).to_contain("\\int")
```

</details>

#### integral through markdown renderer

#### renders integral via to_md

- renders integral via to_md


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders integral via to_md")
val result = to_md("int(t, 0..1) t")
expect(result).to_start_with("$")
expect(result).to_contain("t")
```

</details>

### math_repr renderer edge cases

#### negative idx through render paths

#### neg of number exercises right=-1 path in text

- neg of number exercises right=-1 path in text
   - Expected: result equals `-42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("neg of number exercises right=-1 path in text")
# Neg node has right=-1, when rendering text it calls _render_text(left) only
val result = to_text("-42")
expect(result).to_equal("-42")
```

</details>

#### neg of expr exercises render in debug

- neg of expr exercises render in debug
   - Expected: result equals `Neg(Num(42))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("neg of expr exercises render in debug")
val result = to_debug("-42")
expect(result).to_equal("Neg(Num(42))")
```

</details>

#### neg exercises render in pretty

- neg exercises render in pretty
   - Expected: result equals `-42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("neg exercises render in pretty")
val result = to_pretty("-42")
expect(result).to_equal("-42")
```

</details>

#### neg exercises render in latex

- neg exercises render in latex
   - Expected: result equals `-42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("neg exercises render in latex")
val result = render_latex_raw("-42")
expect(result).to_equal("-42")
```

</details>

#### transpose exercises right=-1 in all renderers

#### transpose in text

- transpose in text
   - Expected: result equals `x'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transpose in text")
val result = to_text("x'")
expect(result).to_equal("x'")
```

</details>

#### transpose in debug

- transpose in debug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transpose in debug")
val result = to_debug("x'")
expect(result).to_contain("Transpose")
```

</details>

#### transpose in pretty

- transpose in pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transpose in pretty")
val result = to_pretty("x'")
expect(result).to_contain("ᵀ")
```

</details>

#### transpose in latex

- transpose in latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transpose in latex")
val result = render_latex_raw("A'")
expect(result).to_contain("T")
```

</details>

### math_repr superscript operator chars

#### superscript plus minus equals parens

#### exercises superscript + via power

- exercises superscript + via power


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises superscript + via power")
val result = to_pretty("x^(n+1)")
expect(result).to_contain("x")
```

</details>

#### exercises superscript - via power

- exercises superscript - via power


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises superscript - via power")
val result = to_pretty("x^(n-1)")
expect(result).to_contain("x")
```

</details>

#### exercises superscript = via power

- exercises superscript = via power


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises superscript = via power")
# Use grouped exponent with equals-like expression
val result = to_pretty("x^(a=b)")
expect(result).to_contain("x")
```

</details>

#### subscript plus minus

#### exercises subscript + via subscript

- exercises subscript + via subscript


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises subscript + via subscript")
val result = to_pretty("x[i+1]")
expect(result).to_contain("x")
```

</details>

#### exercises subscript - via subscript

- exercises subscript - via subscript


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises subscript - via subscript")
val result = to_pretty("x[i-1]")
expect(result).to_contain("x")
```

</details>

### math_repr full renderer node coverage

#### add through all renderers

#### add via pretty

- add via pretty
   - Expected: result equals `a + b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add via pretty")
val result = to_pretty("a + b")
expect(result).to_equal("a + b")
```

</details>

#### add via latex

- add via latex
   - Expected: result equals `a + b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add via latex")
val result = render_latex_raw("a + b")
expect(result).to_equal("a + b")
```

</details>

#### sub through all renderers

#### sub via text

- sub via text
   - Expected: result equals `a - b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sub via text")
val result = to_text("a - b")
expect(result).to_equal("a - b")
```

</details>

#### sub via debug

- sub via debug
   - Expected: result equals `Sub(Id(a), Id(b))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sub via debug")
val result = to_debug("a - b")
expect(result).to_equal("Sub(Id(a), Id(b))")
```

</details>

#### sub via pretty

- sub via pretty
   - Expected: result equals `a - b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sub via pretty")
val result = to_pretty("a - b")
expect(result).to_equal("a - b")
```

</details>

#### sub via latex

- sub via latex
   - Expected: result equals `a - b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sub via latex")
val result = render_latex_raw("a - b")
expect(result).to_equal("a - b")
```

</details>

#### mul explicit through all renderers

#### mul via text

- mul via text
   - Expected: result equals `a * b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mul via text")
val result = to_text("a * b")
expect(result).to_equal("a * b")
```

</details>

#### mul via debug

- mul via debug
   - Expected: result equals `Mul(Id(a), Id(b))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mul via debug")
val result = to_debug("a * b")
expect(result).to_equal("Mul(Id(a), Id(b))")
```

</details>

#### mul via pretty

- mul via pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mul via pretty")
val result = to_pretty("a * b")
expect(result).to_contain("*")
```

</details>

#### mul implicit through all renderers

#### implicit mul via text

- implicit mul via text
   - Expected: result equals `2x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("implicit mul via text")
val result = to_text("2x")
expect(result).to_equal("2x")
```

</details>

#### implicit mul via pretty

- implicit mul via pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("implicit mul via pretty")
val result = to_pretty("2x")
expect(result).to_contain("2")
```

</details>

#### implicit mul via latex

- implicit mul via latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("implicit mul via latex")
val result = render_latex_raw("2x")
expect(result).to_contain("x")
```

</details>

#### div through all renderers

#### div via text

- div via text
   - Expected: result equals `a / b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("div via text")
val result = to_text("a / b")
expect(result).to_equal("a / b")
```

</details>

#### div via debug

- div via debug
   - Expected: result equals `Div(Id(a), Id(b))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("div via debug")
val result = to_debug("a / b")
expect(result).to_equal("Div(Id(a), Id(b))")
```

</details>

#### pow through all renderers

#### pow via text

- pow via text
   - Expected: result equals `a^b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pow via text")
val result = to_text("a^b")
expect(result).to_equal("a^b")
```

</details>

#### pow via debug

- pow via debug
   - Expected: result equals `Pow(Id(a), Id(b))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pow via debug")
val result = to_debug("a^b")
expect(result).to_equal("Pow(Id(a), Id(b))")
```

</details>

#### pow via pretty

- pow via pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pow via pretty")
val result = to_pretty("a^b")
expect(result).to_contain("a")
```

</details>

#### pow via latex

- pow via latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pow via latex")
val result = render_latex_raw("a^b")
expect(result).to_contain("a")
```

</details>

#### neg through all renderers

#### neg via text

- neg via text
   - Expected: result equals `-a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("neg via text")
val result = to_text("-a")
expect(result).to_equal("-a")
```

</details>

#### neg via debug

- neg via debug
   - Expected: result equals `Neg(Id(a))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("neg via debug")
val result = to_debug("-a")
expect(result).to_equal("Neg(Id(a))")
```

</details>

#### neg via pretty

- neg via pretty
   - Expected: result equals `-a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("neg via pretty")
val result = to_pretty("-a")
expect(result).to_equal("-a")
```

</details>

#### neg via latex

- neg via latex
   - Expected: result equals `-a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("neg via latex")
val result = render_latex_raw("-a")
expect(result).to_equal("-a")
```

</details>

#### frac through all renderers

#### frac via text

- frac via text
   - Expected: result equals `a / b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frac via text")
val result = to_text("frac(a, b)")
expect(result).to_equal("a / b")
```

</details>

#### frac via debug

- frac via debug
   - Expected: result equals `Frac(Id(a), Id(b))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frac via debug")
val result = to_debug("frac(a, b)")
expect(result).to_equal("Frac(Id(a), Id(b))")
```

</details>

#### group through all renderers

#### group via text

- group via text
   - Expected: result equals `(a)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("group via text")
val result = to_text("(a)")
expect(result).to_equal("(a)")
```

</details>

#### group via latex

- group via latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("group via latex")
val result = render_latex_raw("(a)")
expect(result).to_contain("(")
```

</details>

#### subscript through all renderers

#### subscript via text

- subscript via text
   - Expected: result equals `a[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subscript via text")
val result = to_text("a[i]")
expect(result).to_equal("a[i]")
```

</details>

#### subscript via pretty

- subscript via pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subscript via pretty")
val result = to_pretty("a[i]")
expect(result).to_contain("a")
```

</details>

#### subscript via latex

- subscript via latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subscript via latex")
val result = render_latex_raw("a[i]")
expect(result).to_contain("a")
```

</details>

#### transpose through all renderers

#### transpose via text

- transpose via text
   - Expected: result equals `A'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transpose via text")
val result = to_text("A'")
expect(result).to_equal("A'")
```

</details>

#### transpose via debug

- transpose via debug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transpose via debug")
val result = to_debug("A'")
expect(result).to_contain("Transpose")
```

</details>

#### call through all renderers

#### call via text

- call via text
   - Expected: result equals `f(x)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("call via text")
val result = to_text("f(x)")
expect(result).to_equal("f(x)")
```

</details>

#### call via pretty

- call via pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("call via pretty")
val result = to_pretty("f(x)")
expect(result).to_contain("f")
```

</details>

#### call via latex known fn

- call via latex known fn


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("call via latex known fn")
val result = render_latex_raw("sin(x)")
expect(result).to_contain("\\sin")
```

</details>

#### call via latex unknown fn

- call via latex unknown fn


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("call via latex unknown fn")
val result = render_latex_raw("foo(x)")
expect(result).to_contain("foo")
```

</details>

#### sum_expr through all renderers

#### sum via text

- sum via text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sum via text")
val result = to_text("sum(i, 1..n) i")
expect(result).to_contain("sum")
```

</details>

#### sum via debug

- sum via debug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sum via debug")
val result = to_debug("sum(i, 1..n) i")
expect(result).to_contain("Sum")
```

</details>

#### sum via pretty

- sum via pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sum via pretty")
val result = to_pretty("sum(i, 1..n) i")
expect(result).to_contain("i")
```

</details>

#### sum via latex

- sum via latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sum via latex")
val result = render_latex_raw("sum(i, 1..n) i")
expect(result).to_contain("\\sum")
```

</details>

#### sum via md

- sum via md


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sum via md")
val result = to_md("sum(i, 1..n) i")
expect(result).to_start_with("$")
```

</details>

#### int_expr through all renderers

#### int via text

- int via text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("int via text")
val result = to_text("int(x, 0..1) x")
expect(result).to_contain("int")
```

</details>

#### int via debug

- int via debug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("int via debug")
val result = to_debug("int(x, 0..1) x")
expect(result).to_contain("Int")
```

</details>

#### int via pretty

- int via pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("int via pretty")
val result = to_pretty("int(x, 0..1) x")
expect(result).to_contain("x")
```

</details>

#### int via latex

- int via latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("int via latex")
val result = render_latex_raw("int(x, 0..1) x")
expect(result).to_contain("x")
```

</details>

#### sqrt call special case

#### sqrt via pretty

- sqrt via pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sqrt via pretty")
val result = to_pretty("sqrt(x)")
expect(result).to_contain("x")
```

</details>

#### sqrt via latex

- sqrt via latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sqrt via latex")
val result = render_latex_raw("sqrt(x)")
expect(result).to_contain("\\sqrt")
```

</details>

#### sqrt via text

- sqrt via text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sqrt via text")
val result = to_text("sqrt(x)")
expect(result).to_contain("sqrt")
```

</details>

#### sqrt via debug

- sqrt via debug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sqrt via debug")
val result = to_debug("sqrt(x)")
expect(result).to_contain("Call")
```

</details>

### math_repr greek function false paths

#### non-greek through pretty

#### non-greek name passes through _resolve_greek unchanged

- non-greek name passes through _resolve_greek unchanged
   - Expected: result equals `myvar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-greek name passes through _resolve_greek unchanged")
val result = to_pretty("myvar")
expect(result).to_equal("myvar")
```

</details>

#### non-greek through latex

#### non-greek name passes through _latex_greek unchanged

- non-greek name passes through _latex_greek unchanged
   - Expected: result equals `myvar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-greek name passes through _latex_greek unchanged")
val result = render_latex_raw("myvar")
expect(result).to_equal("myvar")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 105 |
| Active scenarios | 105 |
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

- Canonical SPipe generation for source `37793f2706dd7ba221753e06c104cadff3ba687f2504a5ce1bdb4b58f000908d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `37793f2706dd7ba221753e06c104cadff3ba687f2504a5ce1bdb4b58f000908d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `37793f2706dd7ba221753e06c104cadff3ba687f2504a5ce1bdb4b58f000908d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/math_repr_pretty_latex_spec.spl
mirror: doc/06_spec/01_unit/lib/common/math_repr_pretty_latex_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/math_repr_pretty_latex_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/math_repr_pretty_latex_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/math_repr_pretty_latex_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders number unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math_repr_pretty_latex_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders plain identifier' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math_repr_pretty_latex_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves lowercase greek' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
