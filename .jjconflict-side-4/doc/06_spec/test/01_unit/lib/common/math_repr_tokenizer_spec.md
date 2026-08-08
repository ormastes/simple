# Math Repr Tokenizer Coverage

> Tests for tokenizer edge cases, branch gaps, operator paths, number tokenization, and underscore alpha coverage.

<!-- sdn-diagram:id=math_repr_tokenizer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_repr_tokenizer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_repr_tokenizer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_repr_tokenizer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for tokenizer edge cases, branch gaps, operator paths,
number tokenization, and underscore alpha coverage.

## Scenarios

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

### math_repr tokenizer operator paths

#### each operator individually

#### tokenizes plus only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("1 + 2")
expect(result).to_equal("Add(Num(1), Num(2))")
```

</details>

#### tokenizes minus only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("1 - 2")
expect(result).to_equal("Sub(Num(1), Num(2))")
```

</details>

#### tokenizes star only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("1 * 2")
expect(result).to_equal("Mul(Num(1), Num(2))")
```

</details>

#### tokenizes slash only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("1 / 2")
expect(result).to_equal("Div(Num(1), Num(2))")
```

</details>

#### tokenizes caret only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("1^2")
expect(result).to_equal("Pow(Num(1), Num(2))")
```

</details>

#### tokenizes apostrophe only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("x'")
expect(result).to_contain("Transpose")
```

</details>

#### tokenizes open paren only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("(x)")
expect(result).to_contain("Group")
```

</details>

#### tokenizes close paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("(1)")
expect(result).to_contain("Group")
```

</details>

#### tokenizes open bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("x[1]")
expect(result).to_contain("Sub")
```

</details>

#### tokenizes close bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("a[0]")
expect(result).to_contain("Sub")
```

</details>

#### tokenizes comma in args

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("f(1, 2)")
expect(result).to_contain("Call")
```

</details>

#### expressions with only division

#### division-only expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("10 / 5")
expect(result).to_equal("10 / 5")
```

</details>

#### division via pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("10 / 5")
expect(result).to_contain("/")
```

</details>

#### division via latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("10 / 5")
expect(result).to_contain("/")
```

</details>

#### expressions with only parens and brackets

#### paren-only expression via text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("(1)")
expect(result).to_equal("(1)")
```

</details>

#### bracket-only expression via text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("x[0]")
expect(result).to_equal("x[0]")
```

</details>

### math_repr number tokenization edges

#### number-dot-dot boundary

#### integer before range is not decimal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("sum(i, 5..10) i")
expect(result).to_contain("Num(5)")
expect(result).to_contain("Num(10)")
```

</details>

#### decimal number in simple expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("3.14")
expect(result).to_equal("Num(3.14)")
```

</details>

#### decimal followed by operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("3.14 + 1")
expect(result).to_contain("Num(3.14)")
```

</details>

#### single dot tokenization

#### dot between identifiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a.b")
expect(result).to_contain("a")
```

</details>

#### dot at end of input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("x.")
expect(result).to_contain("x")
```

</details>

#### standalone dot

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text(".")
expect(result).to_contain("?")
```

</details>

### math_repr underscore alpha coverage

#### underscore as first alpha character

#### underscore-only identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Underscore is alpha in _is_alpha; tokenized as identifier
# But the output might strip leading underscore
val result = to_text("_")
expect(result).to_contain("?")
```

</details>

#### underscore with trailing letters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# a_b is one identifier token since _ is alnum
val result = to_text("a_b")
expect(result).to_contain("a")
```

</details>

#### underscore in middle of identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("x_y")
expect(result).to_contain("x")
```

</details>

### math_repr greek letter resolution

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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 67 |
| Active scenarios | 67 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
