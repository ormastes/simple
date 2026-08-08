# Math Repr Pretty, LaTeX, and Renderer Symbols

> Tests for to_pretty, to_md, render_latex_raw, empty fallbacks, int_expr paths, renderer edge cases, superscript/subscript chars, and greek symbols.

<!-- sdn-diagram:id=math_repr_pretty_latex_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_repr_pretty_latex_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_repr_pretty_latex_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_repr_pretty_latex_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for to_pretty, to_md, render_latex_raw, empty fallbacks,
int_expr paths, renderer edge cases, superscript/subscript chars, and greek symbols.

## Scenarios

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

#### renders transpose with Unicode T suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("A'")
expect(result).to_contain("A")
expect(result).to_contain("ᵀ")
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

### math_repr int_expr all renderers

#### integral through text renderer

#### renders integral via to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("int(t, 0..1) t")
expect(result).to_contain("int")
expect(result).to_contain("t")
```

</details>

#### integral through debug renderer

#### renders integral via to_debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("int(t, 0..1) t")
expect(result).to_contain("Int")
```

</details>

#### integral through pretty renderer

#### renders integral via to_pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("int(t, 0..1) t")
expect(result).to_contain("t")
```

</details>

#### integral through latex renderer

#### renders integral via render_latex_raw

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("int(t, 0..1) t")
expect(result).to_contain("\\int")
```

</details>

#### integral through markdown renderer

#### renders integral via to_md

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_md("int(t, 0..1) t")
expect(result).to_start_with("$")
expect(result).to_contain("t")
```

</details>

### math_repr renderer edge cases

#### negative idx through render paths

#### neg of number exercises right=-1 path in text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Neg node has right=-1, when rendering text it calls _render_text(left) only
val result = to_text("-42")
expect(result).to_equal("-42")
```

</details>

#### neg of expr exercises render in debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("-42")
expect(result).to_equal("Neg(Num(42))")
```

</details>

#### neg exercises render in pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("-42")
expect(result).to_equal("-42")
```

</details>

#### neg exercises render in latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("-42")
expect(result).to_equal("-42")
```

</details>

#### transpose exercises right=-1 in all renderers

#### transpose in text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("x'")
expect(result).to_equal("x'")
```

</details>

#### transpose in debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("x'")
expect(result).to_contain("Transpose")
```

</details>

#### transpose in pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("x'")
expect(result).to_contain("ᵀ")
```

</details>

#### transpose in latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("A'")
expect(result).to_contain("T")
```

</details>

### math_repr superscript operator chars

#### superscript plus minus equals parens

#### exercises superscript + via power

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("x^(n+1)")
expect(result).to_contain("x")
```

</details>

#### exercises superscript - via power

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("x^(n-1)")
expect(result).to_contain("x")
```

</details>

#### exercises superscript = via power

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Use grouped exponent with equals-like expression
val result = to_pretty("x^(a=b)")
expect(result).to_contain("x")
```

</details>

#### subscript plus minus

#### exercises subscript + via subscript

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("x[i+1]")
expect(result).to_contain("x")
```

</details>

#### exercises subscript - via subscript

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("x[i-1]")
expect(result).to_contain("x")
```

</details>

### math_repr full renderer node coverage

#### add through all renderers

#### add via pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("a + b")
expect(result).to_equal("a + b")
```

</details>

#### add via latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("a + b")
expect(result).to_equal("a + b")
```

</details>

#### sub through all renderers

#### sub via text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a - b")
expect(result).to_equal("a - b")
```

</details>

#### sub via debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("a - b")
expect(result).to_equal("Sub(Id(a), Id(b))")
```

</details>

#### sub via pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("a - b")
expect(result).to_equal("a - b")
```

</details>

#### sub via latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("a - b")
expect(result).to_equal("a - b")
```

</details>

#### mul explicit through all renderers

#### mul via text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a * b")
expect(result).to_equal("a * b")
```

</details>

#### mul via debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("a * b")
expect(result).to_equal("Mul(Id(a), Id(b))")
```

</details>

#### mul via pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("a * b")
expect(result).to_contain("*")
```

</details>

#### mul implicit through all renderers

#### implicit mul via text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("2x")
expect(result).to_equal("2x")
```

</details>

#### implicit mul via pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("2x")
expect(result).to_contain("2")
```

</details>

#### implicit mul via latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("2x")
expect(result).to_contain("x")
```

</details>

#### div through all renderers

#### div via text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a / b")
expect(result).to_equal("a / b")
```

</details>

#### div via debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("a / b")
expect(result).to_equal("Div(Id(a), Id(b))")
```

</details>

#### pow through all renderers

#### pow via text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a^b")
expect(result).to_equal("a^b")
```

</details>

#### pow via debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("a^b")
expect(result).to_equal("Pow(Id(a), Id(b))")
```

</details>

#### pow via pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("a^b")
expect(result).to_contain("a")
```

</details>

#### pow via latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("a^b")
expect(result).to_contain("a")
```

</details>

#### neg through all renderers

#### neg via text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("-a")
expect(result).to_equal("-a")
```

</details>

#### neg via debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("-a")
expect(result).to_equal("Neg(Id(a))")
```

</details>

#### neg via pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("-a")
expect(result).to_equal("-a")
```

</details>

#### neg via latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("-a")
expect(result).to_equal("-a")
```

</details>

#### frac through all renderers

#### frac via text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("frac(a, b)")
expect(result).to_equal("a / b")
```

</details>

#### frac via debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("frac(a, b)")
expect(result).to_equal("Frac(Id(a), Id(b))")
```

</details>

#### group through all renderers

#### group via text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("(a)")
expect(result).to_equal("(a)")
```

</details>

#### group via latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("(a)")
expect(result).to_contain("(")
```

</details>

#### subscript through all renderers

#### subscript via text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a[i]")
expect(result).to_equal("a[i]")
```

</details>

#### subscript via pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("a[i]")
expect(result).to_contain("a")
```

</details>

#### subscript via latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("a[i]")
expect(result).to_contain("a")
```

</details>

#### transpose through all renderers

#### transpose via text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("A'")
expect(result).to_equal("A'")
```

</details>

#### transpose via debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("A'")
expect(result).to_contain("Transpose")
```

</details>

#### call through all renderers

#### call via text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("f(x)")
expect(result).to_equal("f(x)")
```

</details>

#### call via pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("f(x)")
expect(result).to_contain("f")
```

</details>

#### call via latex known fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("sin(x)")
expect(result).to_contain("\\sin")
```

</details>

#### call via latex unknown fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("foo(x)")
expect(result).to_contain("foo")
```

</details>

#### sum_expr through all renderers

#### sum via text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("sum(i, 1..n) i")
expect(result).to_contain("sum")
```

</details>

#### sum via debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("sum(i, 1..n) i")
expect(result).to_contain("Sum")
```

</details>

#### sum via pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("sum(i, 1..n) i")
expect(result).to_contain("i")
```

</details>

#### sum via latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("sum(i, 1..n) i")
expect(result).to_contain("\\sum")
```

</details>

#### sum via md

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_md("sum(i, 1..n) i")
expect(result).to_start_with("$")
```

</details>

#### int_expr through all renderers

#### int via text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("int(x, 0..1) x")
expect(result).to_contain("int")
```

</details>

#### int via debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("int(x, 0..1) x")
expect(result).to_contain("Int")
```

</details>

#### int via pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("int(x, 0..1) x")
expect(result).to_contain("x")
```

</details>

#### int via latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("int(x, 0..1) x")
expect(result).to_contain("x")
```

</details>

#### sqrt call special case

#### sqrt via pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("sqrt(x)")
expect(result).to_contain("x")
```

</details>

#### sqrt via latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("sqrt(x)")
expect(result).to_contain("\\sqrt")
```

</details>

#### sqrt via text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("sqrt(x)")
expect(result).to_contain("sqrt")
```

</details>

#### sqrt via debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("sqrt(x)")
expect(result).to_contain("Call")
```

</details>

### math_repr greek function false paths

#### non-greek through pretty

#### non-greek name passes through _resolve_greek unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("myvar")
expect(result).to_equal("myvar")
```

</details>

#### non-greek through latex

#### non-greek name passes through _latex_greek unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
