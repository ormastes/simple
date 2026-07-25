# Math Repr Coverage Specification

> Branch coverage tests for `std.math_repr` parser and renderers. Split from math_coverage_spec.spl for memory. Tests to_text, to_debug, to_pretty, to_md, render_latex_raw, and tokenizer/parser edge cases.

<!-- sdn-diagram:id=math_repr_formats_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_repr_formats_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_repr_formats_coverage_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_repr_formats_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 116 | 116 | 0 | 0 |

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
| Source | `test/01_unit/lib/common/math_repr_formats_coverage_spec.spl` |
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
expect(result).to_contain("T")
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

### math_repr tokenizer branch gaps

#### dot followed by non-dot character

#### handles dot followed by identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("x.y")
expect(result).to_contain("x")
```

</details>

#### decimal number before range

#### handles number with decimal part

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("3.14")
expect(result).to_equal("3.14")
```

</details>

#### division operator tokenization

#### tokenizes division in complex expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a / b + c")
expect(result).to_contain("/")
```

</details>

#### tokenizes multiple divisions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a / b / c")
expect(result).to_contain("/")
```

</details>

#### parentheses tokenization

#### tokenizes nested parens

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("((a + b))")
expect(result).to_contain("(")
expect(result).to_contain(")")
```

</details>

#### bracket tokenization standalone

#### tokenizes brackets in subscript

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a[b]")
expect(result).to_contain("[")
expect(result).to_contain("]")
```

</details>

#### comma tokenization

#### tokenizes commas in multi-arg function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("f(a, b, c)")
expect(result).to_contain(",")
```

</details>

#### unknown character skipping

#### skips at sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a @ b")
expect(result).to_contain("a")
```

</details>

#### skips hash character

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a # b")
expect(result).to_contain("a")
```

</details>

#### underscore in identifiers

#### tokenizes identifier starting with underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("_x")
expect(result).to_contain("x")
```

</details>

#### tokenizes identifier with embedded underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a_b")
expect(result).to_contain("a")
```

</details>

#### is_alnum exercising is_digit false then is_alpha

#### exercises alnum branch for letter after number in ident

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("x1y")
expect(result).to_contain("x1y")
```

</details>

### math_repr parser edge cases deeper

#### frac without comma

#### handles frac with space separation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("frac(a b)")
expect(result).to_contain("a")
```

</details>

#### sum without range

#### handles sum expression completely

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("sum(k, 1..n) k^2")
expect(result).to_contain("Sum")
expect(result).to_contain("Pow")
```

</details>

#### can_start_expr false for non-expression tokens

#### handles expression ending at eof

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("x +")
expect(result).to_contain("Id(x)")
```

</details>

#### implicit mul variations

#### identifier followed by paren group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("a(b + c)")
expect(result).to_contain("Call")
```

</details>

#### paren group followed by identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("(a)b")
expect(result).to_contain("Mul")
expect(result).to_contain("Group")
```

</details>

#### multi-arg function calls through all renderers

#### renders multi-arg call through pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("f(a, b, c)")
expect(result).to_contain("f")
expect(result).to_contain("a")
```

</details>

#### renders multi-arg call through latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("f(a, b, c)")
expect(result).to_contain("f")
```

</details>

#### sqrt through latex

#### renders sqrt in latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("sqrt(x)")
expect(result).to_contain("\\sqrt")
```

</details>

#### frac through all renderers

#### frac through debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("frac(x, y)")
expect(result).to_contain("Frac")
```

</details>

#### frac through pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("frac(x, y)")
expect(result).to_contain("x")
expect(result).to_contain("y")
```

</details>

#### frac through latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("frac(x, y)")
expect(result).to_contain("\\frac")
```

</details>

#### subscript through all renderers

#### subscript through text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a[0]")
expect(result).to_equal("a[0]")
```

</details>

#### subscript through debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("a[0]")
expect(result).to_contain("Sub")
```

</details>

#### subscript through latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("a[0]")
expect(result).to_contain("_")
```

</details>

#### group through all renderers

#### group through debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("(a)")
expect(result).to_contain("Group")
```

</details>

#### group through pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("(a)")
expect(result).to_start_with("(")
expect(result).to_end_with(")")
```

</details>

#### group through latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("(a)")
expect(result).to_start_with("(")
```

</details>

#### division through all renderers

#### div through pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("a / b")
expect(result).to_contain("/")
```

</details>

#### div through latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("a / b")
expect(result).to_contain("/")
```

</details>

#### explicit mul through latex

#### explicit mul renders cdot in latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("a * b")
expect(result).to_contain("\\cdot")
```

</details>

#### implicit mul through latex

#### implicit mul renders space in latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("2x")
expect(result).to_contain("2")
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

### math_repr additional parser coverage

#### postfix chaining

#### multiple subscripts chained

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("a[i][j]")
expect(result).to_contain("Sub")
```

</details>

#### transpose after group

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("(a)'")
expect(result).to_contain("Transpose")
expect(result).to_contain("Group")
```

</details>

#### function with zero args through all renderers

#### zero-arg call via debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("f()")
expect(result).to_contain("Call")
```

</details>

#### zero-arg call via pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("f()")
expect(result).to_contain("f")
```

</details>

#### zero-arg call via latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("f()")
expect(result).to_contain("f")
```

</details>

#### deeply nested expressions

#### nested power and mul

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("x^2 * y^3")
expect(result).to_contain("^")
```

</details>

#### add then sub then mul

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("a + b - c * d")
expect(result).to_contain("Sub")
expect(result).to_contain("Mul")
```

</details>

#### single dot at end of input

#### dot at very end

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a.")
expect(result).to_contain("a")
```

</details>

#### number at end without operator

#### bare number through all renderers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result1 = to_pretty("42")
expect(result1).to_equal("42")
val result2 = render_latex_raw("42")
expect(result2).to_equal("42")
```

</details>

#### complex expressions through pretty and latex

#### power of sum through pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("(a + b)^2")
expect(result).to_contain("a")
```

</details>

#### power of sum through latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("(a + b)^2")
expect(result).to_contain("a")
```

</details>

#### fraction in sum through pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("frac(x, y) + 1")
expect(result).to_contain("x")
```

</details>

#### fraction in sum through latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("frac(x, y) + 1")
expect(result).to_contain("x")
```

</details>

#### multi-char exponent through latex

#### multi-char exponent uses braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("x^(n+1)")
expect(result).to_contain("x")
```

</details>

#### multi-char subscript through latex

#### multi-char subscript uses braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("a[ij]")
expect(result).to_contain("a")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 116 |
| Active scenarios | 116 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
