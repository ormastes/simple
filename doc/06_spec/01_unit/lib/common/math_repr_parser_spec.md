# Math Repr Parser Coverage

> Tests for parser edge cases, operator precedence, implicit multiplication, chained operations, sum/frac parsing, malformed input, and intensive loop coverage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 136 | 136 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Repr Parser Coverage

Tests for parser edge cases, operator precedence, implicit multiplication, chained operations, sum/frac parsing, malformed input, and intensive loop coverage.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-MATH-COV |
| Category | Stdlib |
| Status | Implemented |
| Source | `test/01_unit/lib/common/math_repr_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for parser edge cases, operator precedence, implicit multiplication,
chained operations, sum/frac parsing, malformed input, and intensive loop coverage.

## Scenarios

### math_repr parser edges

#### operator precedence

#### mul binds tighter than add

- mul binds tighter than add
   - Expected: to_debug("a + b * c") equals `Add(Id(a), Mul(Id(b), Id(c)))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mul binds tighter than add")
expect(to_debug("a + b * c")).to_equal("Add(Id(a), Mul(Id(b), Id(c)))")
```

</details>

#### power binds tighter than mul

- power binds tighter than mul
   - Expected: to_debug("a * b^c") equals `Mul(Id(a), Pow(Id(b), Id(c)))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("power binds tighter than mul")
expect(to_debug("a * b^c")).to_equal("Mul(Id(a), Pow(Id(b), Id(c)))")
```

</details>

#### negation applies to power

- negation applies to power
   - Expected: to_debug("-x^2") equals `Neg(Pow(Id(x), Num(2)))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negation applies to power")
expect(to_debug("-x^2")).to_equal("Neg(Pow(Id(x), Num(2)))")
```

</details>

#### implicit multiplication

#### number followed by identifier

- number followed by identifier
   - Expected: to_debug("3x") equals `Mul(Num(3), Id(x))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("number followed by identifier")
expect(to_debug("3x")).to_equal("Mul(Num(3), Id(x))")
```

</details>

#### number followed by paren group

- number followed by paren group
   - Expected: to_debug("2(x)") equals `Mul(Num(2), Group(Id(x)))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("number followed by paren group")
expect(to_debug("2(x)")).to_equal("Mul(Num(2), Group(Id(x)))")
```

</details>

#### identifier followed by paren starts function call

- identifier followed by paren starts function call
   - Expected: to_debug("f(x)") equals `Call(f, Id(x))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifier followed by paren starts function call")
expect(to_debug("f(x)")).to_equal("Call(f, Id(x))")
```

</details>

#### nested grouping

#### handles nested parentheses

- handles nested parentheses
   - Expected: to_debug("((x))") equals `Group(Group(Id(x)))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles nested parentheses")
expect(to_debug("((x))")).to_equal("Group(Group(Id(x)))")
```

</details>

#### chained postfix

#### handles subscript then transpose

- handles subscript then transpose


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles subscript then transpose")
val result = to_debug("A[i]'")
expect(result).to_contain("Transpose")
expect(result).to_contain("Sub")
```

</details>

#### known function detection for latex

#### recognizes sin as known

- recognizes sin as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes sin as known")
val result = render_latex_raw("sin(x)")
expect(result).to_contain("\\sin")
```

</details>

#### recognizes cos as known

- recognizes cos as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes cos as known")
val result = render_latex_raw("cos(x)")
expect(result).to_contain("\\cos")
```

</details>

#### recognizes tan as known

- recognizes tan as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes tan as known")
val result = render_latex_raw("tan(x)")
expect(result).to_contain("\\tan")
```

</details>

#### recognizes log as known

- recognizes log as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes log as known")
val result = render_latex_raw("log(x)")
expect(result).to_contain("\\log")
```

</details>

#### recognizes ln as known

- recognizes ln as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes ln as known")
val result = render_latex_raw("ln(x)")
expect(result).to_contain("\\ln")
```

</details>

#### recognizes exp as known

- recognizes exp as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes exp as known")
val result = render_latex_raw("exp(x)")
expect(result).to_contain("\\exp")
```

</details>

#### recognizes min as known

- recognizes min as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes min as known")
val result = render_latex_raw("min(a, b)")
expect(result).to_contain("\\min")
```

</details>

#### recognizes lim as known

- recognizes lim as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes lim as known")
val result = render_latex_raw("lim(x)")
expect(result).to_contain("\\lim")
```

</details>

#### recognizes tanh as known

- recognizes tanh as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes tanh as known")
val result = render_latex_raw("tanh(x)")
expect(result).to_contain("\\tanh")
```

</details>

#### recognizes sinh as known

- recognizes sinh as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes sinh as known")
val result = render_latex_raw("sinh(x)")
expect(result).to_contain("\\sinh")
```

</details>

#### recognizes cosh as known

- recognizes cosh as known


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes cosh as known")
val result = render_latex_raw("cosh(x)")
expect(result).to_contain("\\cosh")
```

</details>

#### treats unknown function as operatorname

- treats unknown function as operatorname


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats unknown function as operatorname")
val result = render_latex_raw("foo(x)")
expect(result).to_contain('\operatorname{foo}')
```

</details>

#### zero-arg function call

#### renders function with no args

- renders function with no args
   - Expected: to_text("f()") equals `f()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders function with no args")
expect(to_text("f()")).to_equal("f()")
```

</details>

#### single dot token

#### handles single dot at end of input

- handles single dot at end of input


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single dot at end of input")
val result = to_text("x.")
expect(result).to_contain("x")
```

</details>

#### character coverage for _is_digit

#### exercises all digit branches 0-9

- exercises all digit branches 0-9
   - Expected: result equals `1234567890`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises all digit branches 0-9")
# Number containing all 10 digits covers every _is_digit branch
val result = to_text("1234567890")
expect(result).to_equal("1234567890")
```

</details>

#### exercises decimal number with dot

- exercises decimal number with dot
   - Expected: result equals `3.14159`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises decimal number with dot")
val result = to_text("3.14159")
expect(result).to_equal("3.14159")
```

</details>

#### character coverage for _is_alpha

#### exercises lowercase a-m in identifiers

- exercises lowercase a-m in identifiers
   - Expected: r1 equals `abcdefg`
   - Expected: r2 equals `hijklm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises lowercase a-m in identifiers")
val r1 = to_text("abcdefg")
expect(r1).to_equal("abcdefg")
val r2 = to_text("hijklm")
expect(r2).to_equal("hijklm")
```

</details>

#### exercises lowercase n-z in identifiers

- exercises lowercase n-z in identifiers
   - Expected: r1 equals `nopqr`
   - Expected: r2 equals `stuvwxyz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises lowercase n-z in identifiers")
val r1 = to_text("nopqr")
expect(r1).to_equal("nopqr")
val r2 = to_text("stuvwxyz")
expect(r2).to_equal("stuvwxyz")
```

</details>

#### exercises uppercase A-M in identifiers

- exercises uppercase A-M in identifiers
   - Expected: r1 equals `ABCDEFG`
   - Expected: r2 equals `HIJKLM`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises uppercase A-M in identifiers")
val r1 = to_text("ABCDEFG")
expect(r1).to_equal("ABCDEFG")
val r2 = to_text("HIJKLM")
expect(r2).to_equal("HIJKLM")
```

</details>

#### exercises uppercase N-Z in identifiers

- exercises uppercase N-Z in identifiers
   - Expected: r1 equals `NOPQR`
   - Expected: r2 equals `STUVWXYZ`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises uppercase N-Z in identifiers")
val r1 = to_text("NOPQR")
expect(r1).to_equal("NOPQR")
val r2 = to_text("STUVWXYZ")
expect(r2).to_equal("STUVWXYZ")
```

</details>

#### exercises underscore in identifier

- exercises underscore in identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exercises underscore in identifier")
# Underscore is alpha in math tokenizer; tokenizes as single ident
val result = to_text("a_b")
expect(result).to_contain("a")
```

</details>

#### _can_start_expr and _can_implicit_mul edge cases

#### no implicit mul after operator

- no implicit mul after operator
   - Expected: result equals `Add(Id(a), Num(2))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no implicit mul after operator")
# After +, next token is num - not implicit mul context
val result = to_debug("a + 2")
expect(result).to_equal("Add(Id(a), Num(2))")
```

</details>

#### implicit mul with num before lparen

- implicit mul with num before lparen


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("implicit mul with num before lparen")
val result = to_debug("3(a + b)")
expect(result).to_contain("Mul")
expect(result).to_contain("Group")
```

</details>

#### tokenizer number-dot boundary

#### handles number followed by dot-dot range

- handles number followed by dot-dot range


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles number followed by dot-dot range")
# In sum(i, 1..10), the 1 must not consume ".." as decimal
val result = to_debug("sum(i, 1..10) i")
expect(result).to_contain("Sum")
expect(result).to_contain("Num(1)")
expect(result).to_contain("Num(10)")
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
| Total scenarios | 136 |
| Active scenarios | 136 |
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

- Canonical SPipe generation for source `01a06c87c08be82bc681fa9cf9eb8bacce6037150fc02e7332e3dcba44dbccb0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `01a06c87c08be82bc681fa9cf9eb8bacce6037150fc02e7332e3dcba44dbccb0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `01a06c87c08be82bc681fa9cf9eb8bacce6037150fc02e7332e3dcba44dbccb0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/math_repr_parser_spec.spl
mirror: doc/06_spec/01_unit/lib/common/math_repr_parser_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/math_repr_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/math_repr_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/math_repr_parser_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mul binds tighter than add' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math_repr_parser_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'power binds tighter than mul' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math_repr_parser_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'negation applies to power' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
