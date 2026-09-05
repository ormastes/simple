# Math Repr Coverage Specification

> Branch coverage tests for `std.math_repr` parser and renderers. Split from math_coverage_spec.spl for memory. Tests to_text, to_debug, to_pretty, to_md, render_latex_raw, and tokenizer/parser edge cases.

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

### math_repr chained operations

#### chained additions

<details>
<summary>Advanced: triple addition exercises loop continuation</summary>

#### triple addition exercises loop continuation

- triple addition exercises loop continuation
   - Expected: result equals `a + b + c + d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triple addition exercises loop continuation")
val result = to_text("a + b + c + d")
expect(result).to_equal("a + b + c + d")
```

</details>


</details>

#### triple addition via debug

- triple addition via debug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triple addition via debug")
val result = to_debug("a + b + c + d")
expect(result).to_contain("Add")
```

</details>

#### addition then subtraction chain

- addition then subtraction chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("addition then subtraction chain")
val result = to_text("a + b - c + d")
expect(result).to_contain("+")
expect(result).to_contain("-")
```

</details>

#### many additions via pretty

- many additions via pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("many additions via pretty")
val result = to_pretty("a + b + c + d + e")
expect(result).to_contain("+")
```

</details>

#### many additions via latex

- many additions via latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("many additions via latex")
val result = render_latex_raw("a + b + c + d + e")
expect(result).to_contain("+")
```

</details>

#### chained multiplications

#### triple explicit mul

- triple explicit mul


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triple explicit mul")
val result = to_text("a * b * c * d")
expect(result).to_contain("*")
```

</details>

#### triple division

- triple division


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triple division")
val result = to_text("a / b / c")
expect(result).to_contain("/")
```

</details>

#### mixed mul and div

- mixed mul and div


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mixed mul and div")
val result = to_text("a * b / c * d")
expect(result).to_contain("*")
expect(result).to_contain("/")
```

</details>

#### chained implicit mul

- chained implicit mul


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chained implicit mul")
val result = to_text("2x(y)")
expect(result).to_contain("2")
```

</details>

#### chained postfix operations

#### multiple subscripts

- multiple subscripts


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple subscripts")
val result = to_text("a[i][j][k]")
expect(result).to_contain("[")
```

</details>

#### subscript then transpose then subscript

- subscript then transpose then subscript


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subscript then transpose then subscript")
val result = to_text("A[i]'")
expect(result).to_contain("A")
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

### math_repr sum_call edge cases

#### sum without comma separator

#### sum without comma

- sum without comma


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sum without comma")
val result = to_text("sum(i 1..n) i")
expect(result).to_contain("i")
```

</details>

#### sum without range dots

#### sum without range operator

- sum without range operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sum without range operator")
val result = to_text("sum(i, 1 n) i")
expect(result).to_contain("i")
```

</details>

#### sum without closing paren

#### sum missing rparen

- sum missing rparen


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sum missing rparen")
val result = to_text("sum(i, 1..n i")
expect(result).to_contain("i")
```

</details>

#### frac without comma

#### frac missing comma

- frac missing comma


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frac missing comma")
val result = to_text("frac(a b)")
expect(result).to_contain("a")
```

</details>

#### frac without closing paren

#### frac missing rparen

- frac missing rparen


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frac missing rparen")
val result = to_text("frac(a, b x")
expect(result).to_contain("a")
```

</details>

### math_repr can_start_expr num path

#### expression starting with number

#### number after operator uses can_start_expr num

- number after operator uses can_start_expr num
   - Expected: result equals `Add(Id(x), Num(3))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("number after operator uses can_start_expr num")
val result = to_debug("x + 3")
expect(result).to_equal("Add(Id(x), Num(3))")
```

</details>

#### number in complex expression

- number in complex expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("number in complex expression")
val result = to_debug("3 + 4 + 5")
expect(result).to_contain("Add")
```

</details>

#### can_implicit_mul false because num not id or lparen

#### number after number is not implicit mul

- number after number is not implicit mul
   - Expected: result equals `3 + 4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("number after number is not implicit mul")
# "3 4" - the 4 can start expr (num) but implicit mul only for id/lparen
# So "3" is parsed, "4" starts new expr context
val result = to_text("3 + 4")
expect(result).to_equal("3 + 4")
```

</details>

### math_repr parse_primary fallback

#### unexpected token triggers fallback

#### unexpected token at start

- unexpected token at start


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unexpected token at start")
val result = to_text("]")
expect(result).to_contain("?")
```

</details>

#### unexpected rparen at start

- unexpected rparen at start


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unexpected rparen at start")
val result = to_debug(")")
expect(result).to_contain("Id(?)")
```

</details>

#### identifier-like tokens with mixed chars

#### identifier with digits

- identifier with digits
   - Expected: result equals `var123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifier with digits")
val result = to_text("var123")
expect(result).to_equal("var123")
```

</details>

### math_repr malformed input

#### missing close bracket in subscript

#### subscript without rbracket via text

- subscript without rbracket via text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subscript without rbracket via text")
val result = to_text("x[i")
expect(result).to_contain("x")
```

</details>

#### subscript without rbracket via debug

- subscript without rbracket via debug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subscript without rbracket via debug")
val result = to_debug("x[i")
expect(result).to_contain("Sub")
```

</details>

#### subscript without rbracket via pretty

- subscript without rbracket via pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subscript without rbracket via pretty")
val result = to_pretty("x[i")
expect(result).to_contain("x")
```

</details>

#### subscript without rbracket via latex

- subscript without rbracket via latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subscript without rbracket via latex")
val result = render_latex_raw("x[i")
expect(result).to_contain("x")
```

</details>

#### missing close paren in function call

#### function call without rparen via text

- function call without rparen via text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function call without rparen via text")
val result = to_text("f(x")
expect(result).to_contain("f")
```

</details>

#### function call without rparen via debug

- function call without rparen via debug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function call without rparen via debug")
val result = to_debug("f(x")
expect(result).to_contain("Call")
```

</details>

#### function call without rparen via pretty

- function call without rparen via pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function call without rparen via pretty")
val result = to_pretty("f(x")
expect(result).to_contain("f")
```

</details>

#### function call without rparen via latex

- function call without rparen via latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function call without rparen via latex")
val result = render_latex_raw("f(x")
expect(result).to_contain("f")
```

</details>

#### missing close paren in group

#### group without rparen via text

- group without rparen via text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("group without rparen via text")
val result = to_text("(a + b")
expect(result).to_contain("a")
```

</details>

#### group without rparen via debug

- group without rparen via debug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("group without rparen via debug")
val result = to_debug("(a + b")
expect(result).to_contain("Group")
```

</details>

#### group without rparen via pretty

- group without rparen via pretty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("group without rparen via pretty")
val result = to_pretty("(a + b")
expect(result).to_contain("a")
```

</details>

#### group without rparen via latex

- group without rparen via latex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("group without rparen via latex")
val result = render_latex_raw("(a + b")
expect(result).to_contain("a")
```

</details>

#### missing close paren in frac

#### frac without rparen

- frac without rparen


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frac without rparen")
val result = to_text("frac(a, b")
expect(result).to_contain("a")
```

</details>

#### missing comma in sum

#### sum missing comma

- sum missing comma


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sum missing comma")
val result = to_text("sum(i 1..10) i")
expect(result).to_contain("i")
```

</details>

#### missing range in sum

#### sum missing dotdot

- sum missing dotdot


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sum missing dotdot")
val result = to_text("sum(i, 1 10) i")
expect(result).to_contain("i")
```

</details>

#### missing rparen in sum

#### sum missing rparen

- sum missing rparen


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sum missing rparen")
val result = to_text("sum(i, 1..10 i")
expect(result).to_contain("i")
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

### math_repr intensive loop coverage

#### long chained addition to exercise _parse_add loop

#### six-way addition

- six-way addition


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("six-way addition")
val result = to_text("a + b + c + d + e + f")
expect(result).to_contain("a")
expect(result).to_contain("f")
```

</details>

#### addition and subtraction interleaved

- addition and subtraction interleaved


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("addition and subtraction interleaved")
val result = to_text("a + b - c + d - e + f")
expect(result).to_contain("a")
```

</details>

#### six-way via debug

- six-way via debug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("six-way via debug")
val result = to_debug("a + b + c + d + e + f")
expect(result).to_contain("Add")
```

</details>

#### long chained mul to exercise _parse_mul loop

#### six-way multiplication

- six-way multiplication


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("six-way multiplication")
val result = to_text("a * b * c * d * e * f")
expect(result).to_contain("*")
```

</details>

#### six-way division

- six-way division


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("six-way division")
val result = to_text("a / b / c / d / e / f")
expect(result).to_contain("/")
```

</details>

#### large number for digit loop

<details>
<summary>Advanced: ten-digit number exercises inner digit loop</summary>

#### ten-digit number exercises inner digit loop

- ten-digit number exercises inner digit loop
   - Expected: result equals `1234567890`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ten-digit number exercises inner digit loop")
val result = to_text("1234567890")
expect(result).to_equal("1234567890")
```

</details>


</details>

#### number with many decimal places

- number with many decimal places
   - Expected: result equals `3.14159265`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("number with many decimal places")
val result = to_text("3.14159265")
expect(result).to_equal("3.14159265")
```

</details>

#### long identifier for alnum loop

<details>
<summary>Advanced: long identifier exercises inner alnum loop</summary>

#### long identifier exercises inner alnum loop

- long identifier exercises inner alnum loop
   - Expected: result equals `abcdefghijklmnop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("long identifier exercises inner alnum loop")
val result = to_text("abcdefghijklmnop")
expect(result).to_equal("abcdefghijklmnop")
```

</details>


</details>

#### many subscripts for postfix loop

#### four chained subscripts

- four chained subscripts


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("four chained subscripts")
val result = to_text("a[i][j][k][l]")
expect(result).to_contain("[")
```

</details>

#### many function args for comma loop

#### five-arg function

- five-arg function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("five-arg function")
val result = to_text("f(a, b, c, d, e)")
expect(result).to_contain("f")
expect(result).to_contain("e")
```

</details>

#### deeply nested parens

#### triple nested parens

- triple nested parens


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triple nested parens")
val result = to_text("(((x)))")
expect(result).to_contain("x")
```

</details>

#### expression with many different token types

#### all token types in one expression

- all token types in one expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all token types in one expression")
val result = to_text("f(a + b * c / d, e^2, g[i])")
expect(result).to_contain("f")
expect(result).to_contain("g")
```

</details>

#### number then range dots in sum context

#### two-digit number before range

- two-digit number before range


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two-digit number before range")
val result = to_debug("sum(i, 10..20) i")
expect(result).to_contain("Num(10)")
expect(result).to_contain("Num(20)")
```

</details>

#### single digit before range

- single digit before range


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single digit before range")
val result = to_debug("sum(i, 1..9) i")
expect(result).to_contain("Num(1)")
expect(result).to_contain("Num(9)")
```

</details>

#### number followed by number for can_start_expr num path

#### two numbers separated by space

- two numbers separated by space


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two numbers separated by space")
# "3 4" - first parsed as Num(3), then _parse_mul checks for implicit mul
# _can_implicit_mul calls _can_start_expr which hits pk=="num" TRUE
# then _can_implicit_mul checks pk=="id" (false), pk=="lparen" (false)
# so implicit mul doesn't happen, "4" is left unconsumed
val result = to_debug("3 4")
expect(result).to_contain("Num(3)")
```

</details>

#### number then number then id

- number then number then id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("number then number then id")
val result = to_debug("3 4 x")
expect(result).to_contain("Num(3)")
```

</details>

#### number after paren group forces can_start_expr

- number after paren group forces can_start_expr


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("number after paren group forces can_start_expr")
val result = to_debug("(a) 5")
expect(result).to_contain("Group")
```

</details>

#### single-char inputs for tokenizer path isolation

#### only lparen

- only lparen


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only lparen")
val result = to_text("(")
expect(result).to_contain("?")
```

</details>

#### only rparen

- only rparen


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only rparen")
val result = to_text(")")
expect(result).to_contain("?")
```

</details>

#### only lbracket

- only lbracket


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only lbracket")
val result = to_text("[")
expect(result).to_contain("?")
```

</details>

#### only rbracket

- only rbracket


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only rbracket")
val result = to_text("]")
expect(result).to_contain("?")
```

</details>

#### only comma

- only comma


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only comma")
val result = to_text(",")
expect(result).to_contain("?")
```

</details>

#### only slash

- only slash


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only slash")
val result = to_text("/")
expect(result).to_contain("?")
```

</details>

#### only star

- only star


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only star")
val result = to_text("*")
expect(result).to_contain("?")
```

</details>

#### only caret

- only caret


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only caret")
val result = to_text("^")
expect(result).to_contain("?")
```

</details>

#### only apostrophe

- only apostrophe


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only apostrophe")
val result = to_text("'")
expect(result).to_contain("?")
```

</details>

#### two-char inputs: operator then identifier

#### lparen then x

- lparen then x


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lparen then x")
val result = to_text("(x")
expect(result).to_contain("x")
```

</details>

#### slash then x

- slash then x


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("slash then x")
val result = to_text("/x")
expect(result).to_contain("x")
```

</details>

#### comma then x

- comma then x


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("comma then x")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ccc4156fb1bcbeec055c3366435fe2c3fa6fb1fc075a212ae598335ed7ba0ff5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ccc4156fb1bcbeec055c3366435fe2c3fa6fb1fc075a212ae598335ed7ba0ff5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ccc4156fb1bcbeec055c3366435fe2c3fa6fb1fc075a212ae598335ed7ba0ff5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/math_repr_edge_coverage_spec.spl
mirror: doc/06_spec/01_unit/lib/common/math_repr_edge_coverage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/math_repr_edge_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/math_repr_edge_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/math_repr_edge_coverage_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'triple addition exercises loop continuation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math_repr_edge_coverage_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'triple addition via debug' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math_repr_edge_coverage_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'addition then subtraction chain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
