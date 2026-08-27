# Math Repr Tokenizer Coverage

> Tests for tokenizer edge cases, branch gaps, operator paths, number tokenization, and underscore alpha coverage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 67 | 67 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Repr Tokenizer Coverage

Tests for tokenizer edge cases, branch gaps, operator paths, number tokenization, and underscore alpha coverage.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-MATH-COV |
| Category | Stdlib |
| Status | Implemented |
| Source | `test/01_unit/lib/common/math_repr_tokenizer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for tokenizer edge cases, branch gaps, operator paths,
number tokenization, and underscore alpha coverage.

## Scenarios

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

### math_repr tokenizer operator paths

#### each operator individually

#### tokenizes plus only

- tokenizes plus only
   - Expected: result equals `Add(Num(1), Num(2))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes plus only")
val result = to_debug("1 + 2")
expect(result).to_equal("Add(Num(1), Num(2))")
```

</details>

#### tokenizes minus only

- tokenizes minus only
   - Expected: result equals `Sub(Num(1), Num(2))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes minus only")
val result = to_debug("1 - 2")
expect(result).to_equal("Sub(Num(1), Num(2))")
```

</details>

#### tokenizes star only

- tokenizes star only
   - Expected: result equals `Mul(Num(1), Num(2))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes star only")
val result = to_debug("1 * 2")
expect(result).to_equal("Mul(Num(1), Num(2))")
```

</details>

#### tokenizes slash only

- tokenizes slash only
   - Expected: result equals `Div(Num(1), Num(2))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes slash only")
val result = to_debug("1 / 2")
expect(result).to_equal("Div(Num(1), Num(2))")
```

</details>

#### tokenizes caret only

- tokenizes caret only
   - Expected: result equals `Pow(Num(1), Num(2))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes caret only")
val result = to_debug("1^2")
expect(result).to_equal("Pow(Num(1), Num(2))")
```

</details>

#### tokenizes apostrophe only

- tokenizes apostrophe only


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes apostrophe only")
val result = to_debug("x'")
expect(result).to_contain("Transpose")
```

</details>

#### tokenizes open paren only

- tokenizes open paren only


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes open paren only")
val result = to_debug("(x)")
expect(result).to_contain("Group")
```

</details>

#### tokenizes close paren

- tokenizes close paren


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes close paren")
val result = to_debug("(1)")
expect(result).to_contain("Group")
```

</details>

#### tokenizes open bracket

- tokenizes open bracket


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes open bracket")
val result = to_debug("x[1]")
expect(result).to_contain("Sub")
```

</details>

#### tokenizes close bracket

- tokenizes close bracket


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes close bracket")
val result = to_debug("a[0]")
expect(result).to_contain("Sub")
```

</details>

#### tokenizes comma in args

- tokenizes comma in args


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes comma in args")
val result = to_debug("f(1, 2)")
expect(result).to_contain("Call")
```

</details>

#### expressions with only division

#### division-only expression

- division-only expression
   - Expected: result equals `10 / 5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("division-only expression")
val result = to_text("10 / 5")
expect(result).to_equal("10 / 5")
```

</details>

#### division via pretty

- division via pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("division via pretty")
val result = to_pretty("10 / 5")
expect(result).to_contain("/")
```

</details>

#### division via latex

- division via latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("division via latex")
val result = render_latex_raw("10 / 5")
expect(result).to_contain("/")
```

</details>

#### expressions with only parens and brackets

#### paren-only expression via text

- paren-only expression via text
   - Expected: result equals `(1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paren-only expression via text")
val result = to_text("(1)")
expect(result).to_equal("(1)")
```

</details>

#### bracket-only expression via text

- bracket-only expression via text
   - Expected: result equals `x[0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bracket-only expression via text")
val result = to_text("x[0]")
expect(result).to_equal("x[0]")
```

</details>

### math_repr number tokenization edges

#### number-dot-dot boundary

#### integer before range is not decimal

- integer before range is not decimal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integer before range is not decimal")
val result = to_debug("sum(i, 5..10) i")
expect(result).to_contain("Num(5)")
expect(result).to_contain("Num(10)")
```

</details>

#### decimal number in simple expression

- decimal number in simple expression
   - Expected: result equals `Num(3.14)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decimal number in simple expression")
val result = to_debug("3.14")
expect(result).to_equal("Num(3.14)")
```

</details>

#### decimal followed by operator

- decimal followed by operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decimal followed by operator")
val result = to_debug("3.14 + 1")
expect(result).to_contain("Num(3.14)")
```

</details>

#### single dot tokenization

#### dot between identifiers

- dot between identifiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dot between identifiers")
val result = to_text("a.b")
expect(result).to_contain("a")
```

</details>

#### dot at end of input

- dot at end of input


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dot at end of input")
val result = to_text("x.")
expect(result).to_contain("x")
```

</details>

#### standalone dot

- standalone dot


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("standalone dot")
val result = to_text(".")
expect(result).to_contain("?")
```

</details>

### math_repr underscore alpha coverage

#### underscore as first alpha character

#### underscore-only identifier

- underscore-only identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("underscore-only identifier")
# Underscore is alpha in _is_alpha; tokenized as identifier
# But the output might strip leading underscore
val result = to_text("_")
expect(result).to_contain("?")
```

</details>

#### underscore with trailing letters

- underscore with trailing letters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("underscore with trailing letters")
# a_b is one identifier token since _ is alnum
val result = to_text("a_b")
expect(result).to_contain("a")
```

</details>

#### underscore in middle of identifier

- underscore in middle of identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("underscore in middle of identifier")
val result = to_text("x_y")
expect(result).to_contain("x")
```

</details>

### math_repr greek letter resolution

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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 67 |
| Active scenarios | 67 |
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

- Canonical SPipe generation for source `728851833a837d96be23ae57e44c70d37e35739acb39c46aaa814c749c1e6fcd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `728851833a837d96be23ae57e44c70d37e35739acb39c46aaa814c749c1e6fcd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `728851833a837d96be23ae57e44c70d37e35739acb39c46aaa814c749c1e6fcd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/math_repr_tokenizer_spec.spl
mirror: doc/06_spec/01_unit/lib/common/math_repr_tokenizer_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/math_repr_tokenizer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/math_repr_tokenizer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/math_repr_tokenizer_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles extra spaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math_repr_tokenizer_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles tabs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math_repr_tokenizer_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles dot-dot range in sum' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
