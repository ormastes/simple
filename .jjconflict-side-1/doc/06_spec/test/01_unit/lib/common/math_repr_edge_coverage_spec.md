# Math Repr Coverage Specification

> Branch coverage tests for `std.math_repr` parser and renderers. Split from math_coverage_spec.spl for memory. Tests to_text, to_debug, to_pretty, to_md, render_latex_raw, and tokenizer/parser edge cases.

<!-- sdn-diagram:id=math_repr_edge_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_repr_edge_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_repr_edge_coverage_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_repr_edge_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 93 | 93 | 0 | 0 |

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
| Source | `test/01_unit/lib/common/math_repr_edge_coverage_spec.spl` |
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

### math_repr chained operations

#### chained additions

<details>
<summary>Advanced: triple addition exercises loop continuation</summary>

#### triple addition exercises loop continuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a + b + c + d")
expect(result).to_equal("a + b + c + d")
```

</details>


</details>

#### triple addition via debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("a + b + c + d")
expect(result).to_contain("Add")
```

</details>

#### addition then subtraction chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a + b - c + d")
expect(result).to_contain("+")
expect(result).to_contain("-")
```

</details>

#### many additions via pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("a + b + c + d + e")
expect(result).to_contain("+")
```

</details>

#### many additions via latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("a + b + c + d + e")
expect(result).to_contain("+")
```

</details>

#### chained multiplications

#### triple explicit mul

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a * b * c * d")
expect(result).to_contain("*")
```

</details>

#### triple division

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a / b / c")
expect(result).to_contain("/")
```

</details>

#### mixed mul and div

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a * b / c * d")
expect(result).to_contain("*")
expect(result).to_contain("/")
```

</details>

#### chained implicit mul

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("2x(y)")
expect(result).to_contain("2")
```

</details>

#### chained postfix operations

#### multiple subscripts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a[i][j][k]")
expect(result).to_contain("[")
```

</details>

#### subscript then transpose then subscript

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("A[i]'")
expect(result).to_contain("A")
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

### math_repr sum_call edge cases

#### sum without comma separator

#### sum without comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("sum(i 1..n) i")
expect(result).to_contain("i")
```

</details>

#### sum without range dots

#### sum without range operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("sum(i, 1 n) i")
expect(result).to_contain("i")
```

</details>

#### sum without closing paren

#### sum missing rparen

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("sum(i, 1..n i")
expect(result).to_contain("i")
```

</details>

#### frac without comma

#### frac missing comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("frac(a b)")
expect(result).to_contain("a")
```

</details>

#### frac without closing paren

#### frac missing rparen

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("frac(a, b x")
expect(result).to_contain("a")
```

</details>

### math_repr can_start_expr num path

#### expression starting with number

#### number after operator uses can_start_expr num

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("x + 3")
expect(result).to_equal("Add(Id(x), Num(3))")
```

</details>

#### number in complex expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("3 + 4 + 5")
expect(result).to_contain("Add")
```

</details>

#### can_implicit_mul false because num not id or lparen

#### number after number is not implicit mul

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "3 4" - the 4 can start expr (num) but implicit mul only for id/lparen
# So "3" is parsed, "4" starts new expr context
val result = to_text("3 + 4")
expect(result).to_equal("3 + 4")
```

</details>

### math_repr parse_primary fallback

#### unexpected token triggers fallback

#### unexpected token at start

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("]")
expect(result).to_contain("?")
```

</details>

#### unexpected rparen at start

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug(")")
expect(result).to_contain("Id(?)")
```

</details>

#### identifier-like tokens with mixed chars

#### identifier with digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("var123")
expect(result).to_equal("var123")
```

</details>

### math_repr malformed input

#### missing close bracket in subscript

#### subscript without rbracket via text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("x[i")
expect(result).to_contain("x")
```

</details>

#### subscript without rbracket via debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("x[i")
expect(result).to_contain("Sub")
```

</details>

#### subscript without rbracket via pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("x[i")
expect(result).to_contain("x")
```

</details>

#### subscript without rbracket via latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("x[i")
expect(result).to_contain("x")
```

</details>

#### missing close paren in function call

#### function call without rparen via text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("f(x")
expect(result).to_contain("f")
```

</details>

#### function call without rparen via debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("f(x")
expect(result).to_contain("Call")
```

</details>

#### function call without rparen via pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("f(x")
expect(result).to_contain("f")
```

</details>

#### function call without rparen via latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("f(x")
expect(result).to_contain("f")
```

</details>

#### missing close paren in group

#### group without rparen via text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("(a + b")
expect(result).to_contain("a")
```

</details>

#### group without rparen via debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("(a + b")
expect(result).to_contain("Group")
```

</details>

#### group without rparen via pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_pretty("(a + b")
expect(result).to_contain("a")
```

</details>

#### group without rparen via latex

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("(a + b")
expect(result).to_contain("a")
```

</details>

#### missing close paren in frac

#### frac without rparen

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("frac(a, b")
expect(result).to_contain("a")
```

</details>

#### missing comma in sum

#### sum missing comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("sum(i 1..10) i")
expect(result).to_contain("i")
```

</details>

#### missing range in sum

#### sum missing dotdot

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("sum(i, 1 10) i")
expect(result).to_contain("i")
```

</details>

#### missing rparen in sum

#### sum missing rparen

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("sum(i, 1..10 i")
expect(result).to_contain("i")
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

### math_repr intensive loop coverage

#### long chained addition to exercise _parse_add loop

#### six-way addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a + b + c + d + e + f")
expect(result).to_contain("a")
expect(result).to_contain("f")
```

</details>

#### addition and subtraction interleaved

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a + b - c + d - e + f")
expect(result).to_contain("a")
```

</details>

#### six-way via debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("a + b + c + d + e + f")
expect(result).to_contain("Add")
```

</details>

#### long chained mul to exercise _parse_mul loop

#### six-way multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a * b * c * d * e * f")
expect(result).to_contain("*")
```

</details>

#### six-way division

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a / b / c / d / e / f")
expect(result).to_contain("/")
```

</details>

#### large number for digit loop

<details>
<summary>Advanced: ten-digit number exercises inner digit loop</summary>

#### ten-digit number exercises inner digit loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("1234567890")
expect(result).to_equal("1234567890")
```

</details>


</details>

#### number with many decimal places

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("3.14159265")
expect(result).to_equal("3.14159265")
```

</details>

#### long identifier for alnum loop

<details>
<summary>Advanced: long identifier exercises inner alnum loop</summary>

#### long identifier exercises inner alnum loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("abcdefghijklmnop")
expect(result).to_equal("abcdefghijklmnop")
```

</details>


</details>

#### many subscripts for postfix loop

#### four chained subscripts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("a[i][j][k][l]")
expect(result).to_contain("[")
```

</details>

#### many function args for comma loop

#### five-arg function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("f(a, b, c, d, e)")
expect(result).to_contain("f")
expect(result).to_contain("e")
```

</details>

#### deeply nested parens

#### triple nested parens

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("(((x)))")
expect(result).to_contain("x")
```

</details>

#### expression with many different token types

#### all token types in one expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("f(a + b * c / d, e^2, g[i])")
expect(result).to_contain("f")
expect(result).to_contain("g")
```

</details>

#### number then range dots in sum context

#### two-digit number before range

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("sum(i, 10..20) i")
expect(result).to_contain("Num(10)")
expect(result).to_contain("Num(20)")
```

</details>

#### single digit before range

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("sum(i, 1..9) i")
expect(result).to_contain("Num(1)")
expect(result).to_contain("Num(9)")
```

</details>

#### number followed by number for can_start_expr num path

#### two numbers separated by space

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "3 4" - first parsed as Num(3), then _parse_mul checks for implicit mul
# _can_implicit_mul calls _can_start_expr which hits pk=="num" TRUE
# then _can_implicit_mul checks pk=="id" (false), pk=="lparen" (false)
# so implicit mul doesn't happen, "4" is left unconsumed
val result = to_debug("3 4")
expect(result).to_contain("Num(3)")
```

</details>

#### number then number then id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("3 4 x")
expect(result).to_contain("Num(3)")
```

</details>

#### number after paren group forces can_start_expr

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("(a) 5")
expect(result).to_contain("Group")
```

</details>

#### single-char inputs for tokenizer path isolation

#### only lparen

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("(")
expect(result).to_contain("?")
```

</details>

#### only rparen

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text(")")
expect(result).to_contain("?")
```

</details>

#### only lbracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("[")
expect(result).to_contain("?")
```

</details>

#### only rbracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("]")
expect(result).to_contain("?")
```

</details>

#### only comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text(",")
expect(result).to_contain("?")
```

</details>

#### only slash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("/")
expect(result).to_contain("?")
```

</details>

#### only star

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("*")
expect(result).to_contain("?")
```

</details>

#### only caret

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("^")
expect(result).to_contain("?")
```

</details>

#### only apostrophe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("'")
expect(result).to_contain("?")
```

</details>

#### two-char inputs: operator then identifier

#### lparen then x

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("(x")
expect(result).to_contain("x")
```

</details>

#### slash then x

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("/x")
expect(result).to_contain("x")
```

</details>

#### comma then x

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text(",x")
expect(result).to_contain("x")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 93 |
| Active scenarios | 93 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
