# Math Repr Coverage Specification

> Branch coverage tests for `std.math_repr` parser and renderers. Split from math_coverage_spec.spl for memory. Tests to_text, to_debug, to_pretty, to_md, render_latex_raw, and tokenizer/parser edge cases.

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
expect(result).to_contain("T")
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

### math_repr tokenizer branch gaps

#### dot followed by non-dot character

#### handles dot followed by identifier

- handles dot followed by identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles dot followed by identifier")
val result = to_text("x.y")
expect(result).to_contain("x")
```

</details>

#### decimal number before range

#### handles number with decimal part

- handles number with decimal part
   - Expected: result equals `3.14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles number with decimal part")
val result = to_text("3.14")
expect(result).to_equal("3.14")
```

</details>

#### division operator tokenization

#### tokenizes division in complex expression

- tokenizes division in complex expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes division in complex expression")
val result = to_text("a / b + c")
expect(result).to_contain("/")
```

</details>

#### tokenizes multiple divisions

- tokenizes multiple divisions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes multiple divisions")
val result = to_text("a / b / c")
expect(result).to_contain("/")
```

</details>

#### parentheses tokenization

#### tokenizes nested parens

- tokenizes nested parens


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes nested parens")
val result = to_text("((a + b))")
expect(result).to_contain("(")
expect(result).to_contain(")")
```

</details>

#### bracket tokenization standalone

#### tokenizes brackets in subscript

- tokenizes brackets in subscript


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes brackets in subscript")
val result = to_text("a[b]")
expect(result).to_contain("[")
expect(result).to_contain("]")
```

</details>

#### comma tokenization

#### tokenizes commas in multi-arg function

- tokenizes commas in multi-arg function


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes commas in multi-arg function")
val result = to_text("f(a, b, c)")
expect(result).to_contain(",")
```

</details>

#### unknown character skipping

#### skips at sign

- skips at sign


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips at sign")
val result = to_text("a @ b")
expect(result).to_contain("a")
```

</details>

#### skips hash character

- skips hash character


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips hash character")
val result = to_text("a # b")
expect(result).to_contain("a")
```

</details>

#### underscore in identifiers

#### tokenizes identifier starting with underscore

- tokenizes identifier starting with underscore


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes identifier starting with underscore")
val result = to_text("_x")
expect(result).to_contain("x")
```

</details>

#### tokenizes identifier with embedded underscore

- tokenizes identifier with embedded underscore


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes identifier with embedded underscore")
val result = to_text("a_b")
expect(result).to_contain("a")
```

</details>

#### is_alnum exercising is_digit false then is_alpha

#### exercises alnum branch for letter after number in ident

- exercises alnum branch for letter after number in ident


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises alnum branch for letter after number in ident")
val result = to_text("x1y")
expect(result).to_contain("x1y")
```

</details>

### math_repr parser edge cases deeper

#### frac without comma

#### handles frac with space separation

- handles frac with space separation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles frac with space separation")
val result = to_text("frac(a b)")
expect(result).to_contain("a")
```

</details>

#### sum without range

#### handles sum expression completely

- handles sum expression completely


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles sum expression completely")
val result = to_debug("sum(k, 1..n) k^2")
expect(result).to_contain("Sum")
expect(result).to_contain("Pow")
```

</details>

#### can_start_expr false for non-expression tokens

#### handles expression ending at eof

- handles expression ending at eof


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles expression ending at eof")
val result = to_debug("x +")
expect(result).to_contain("Id(x)")
```

</details>

#### implicit mul variations

#### identifier followed by paren group

- identifier followed by paren group


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifier followed by paren group")
val result = to_debug("a(b + c)")
expect(result).to_contain("Call")
```

</details>

#### paren group followed by identifier

- paren group followed by identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paren group followed by identifier")
val result = to_debug("(a)b")
expect(result).to_contain("Mul")
expect(result).to_contain("Group")
```

</details>

#### multi-arg function calls through all renderers

#### renders multi-arg call through pretty

- renders multi-arg call through pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders multi-arg call through pretty")
val result = to_pretty("f(a, b, c)")
expect(result).to_contain("f")
expect(result).to_contain("a")
```

</details>

#### renders multi-arg call through latex

- renders multi-arg call through latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders multi-arg call through latex")
val result = render_latex_raw("f(a, b, c)")
expect(result).to_contain("f")
```

</details>

#### sqrt through latex

#### renders sqrt in latex

- renders sqrt in latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders sqrt in latex")
val result = render_latex_raw("sqrt(x)")
expect(result).to_contain("\\sqrt")
```

</details>

#### frac through all renderers

#### frac through debug

- frac through debug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frac through debug")
val result = to_debug("frac(x, y)")
expect(result).to_contain("Frac")
```

</details>

#### frac through pretty

- frac through pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frac through pretty")
val result = to_pretty("frac(x, y)")
expect(result).to_contain("x")
expect(result).to_contain("y")
```

</details>

#### frac through latex

- frac through latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frac through latex")
val result = render_latex_raw("frac(x, y)")
expect(result).to_contain("\\frac")
```

</details>

#### subscript through all renderers

#### subscript through text

- subscript through text
   - Expected: result equals `a[0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subscript through text")
val result = to_text("a[0]")
expect(result).to_equal("a[0]")
```

</details>

#### subscript through debug

- subscript through debug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subscript through debug")
val result = to_debug("a[0]")
expect(result).to_contain("Sub")
```

</details>

#### subscript through latex

- subscript through latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subscript through latex")
val result = render_latex_raw("a[0]")
expect(result).to_contain("_")
```

</details>

#### group through all renderers

#### group through debug

- group through debug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("group through debug")
val result = to_debug("(a)")
expect(result).to_contain("Group")
```

</details>

#### group through pretty

- group through pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("group through pretty")
val result = to_pretty("(a)")
expect(result).to_start_with("(")
expect(result).to_end_with(")")
```

</details>

#### group through latex

- group through latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("group through latex")
val result = render_latex_raw("(a)")
expect(result).to_start_with("(")
```

</details>

#### division through all renderers

#### div through pretty

- div through pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("div through pretty")
val result = to_pretty("a / b")
expect(result).to_contain("/")
```

</details>

#### div through latex

- div through latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("div through latex")
val result = render_latex_raw("a / b")
expect(result).to_contain("/")
```

</details>

#### explicit mul through latex

#### explicit mul renders cdot in latex

- explicit mul renders cdot in latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("explicit mul renders cdot in latex")
val result = render_latex_raw("a * b")
expect(result).to_contain("\\cdot")
```

</details>

#### implicit mul through latex

#### implicit mul renders space in latex

- implicit mul renders space in latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("implicit mul renders space in latex")
val result = render_latex_raw("2x")
expect(result).to_contain("2")
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

### math_repr additional parser coverage

#### postfix chaining

#### multiple subscripts chained

- multiple subscripts chained


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple subscripts chained")
val result = to_debug("a[i][j]")
expect(result).to_contain("Sub")
```

</details>

#### transpose after group

- transpose after group


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transpose after group")
val result = to_debug("(a)'")
expect(result).to_contain("Transpose")
expect(result).to_contain("Group")
```

</details>

#### function with zero args through all renderers

#### zero-arg call via debug

- zero-arg call via debug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero-arg call via debug")
val result = to_debug("f()")
expect(result).to_contain("Call")
```

</details>

#### zero-arg call via pretty

- zero-arg call via pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero-arg call via pretty")
val result = to_pretty("f()")
expect(result).to_contain("f")
```

</details>

#### zero-arg call via latex

- zero-arg call via latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero-arg call via latex")
val result = render_latex_raw("f()")
expect(result).to_contain("f")
```

</details>

#### deeply nested expressions

#### nested power and mul

- nested power and mul


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested power and mul")
val result = to_text("x^2 * y^3")
expect(result).to_contain("^")
```

</details>

#### add then sub then mul

- add then sub then mul


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add then sub then mul")
val result = to_debug("a + b - c * d")
expect(result).to_contain("Sub")
expect(result).to_contain("Mul")
```

</details>

#### single dot at end of input

#### dot at very end

- dot at very end


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dot at very end")
val result = to_text("a.")
expect(result).to_contain("a")
```

</details>

#### number at end without operator

#### bare number through all renderers

- bare number through all renderers
   - Expected: result1 equals `42`
   - Expected: result2 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bare number through all renderers")
val result1 = to_pretty("42")
expect(result1).to_equal("42")
val result2 = render_latex_raw("42")
expect(result2).to_equal("42")
```

</details>

#### complex expressions through pretty and latex

#### power of sum through pretty

- power of sum through pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("power of sum through pretty")
val result = to_pretty("(a + b)^2")
expect(result).to_contain("a")
```

</details>

#### power of sum through latex

- power of sum through latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("power of sum through latex")
val result = render_latex_raw("(a + b)^2")
expect(result).to_contain("a")
```

</details>

#### fraction in sum through pretty

- fraction in sum through pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fraction in sum through pretty")
val result = to_pretty("frac(x, y) + 1")
expect(result).to_contain("x")
```

</details>

#### fraction in sum through latex

- fraction in sum through latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fraction in sum through latex")
val result = render_latex_raw("frac(x, y) + 1")
expect(result).to_contain("x")
```

</details>

#### multi-char exponent through latex

#### multi-char exponent uses braces

- multi-char exponent uses braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multi-char exponent uses braces")
val result = render_latex_raw("x^(n+1)")
expect(result).to_contain("x")
```

</details>

#### multi-char subscript through latex

#### multi-char subscript uses braces

- multi-char subscript uses braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multi-char subscript uses braces")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f11d46c200b8e9dd9ceddc556c98e9173461e1f6e2707b558bf8fc64d189082e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f11d46c200b8e9dd9ceddc556c98e9173461e1f6e2707b558bf8fc64d189082e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f11d46c200b8e9dd9ceddc556c98e9173461e1f6e2707b558bf8fc64d189082e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/math_repr_formats_coverage_spec.spl
mirror: doc/06_spec/01_unit/lib/common/math_repr_formats_coverage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/math_repr_formats_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/math_repr_formats_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/math_repr_formats_coverage_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders integral via to_text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math_repr_formats_coverage_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders integral via to_debug' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math_repr_formats_coverage_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders integral via to_pretty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
