# Math Repr Parser Coverage

> Tests for parser edge cases, operator precedence, implicit multiplication, chained operations, sum/frac parsing, malformed input, and intensive loop coverage.

<!-- sdn-diagram:id=math_repr_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_repr_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_repr_parser_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_repr_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for parser edge cases, operator precedence, implicit multiplication,
chained operations, sum/frac parsing, malformed input, and intensive loop coverage.

## Scenarios

### math_repr parser edges

#### operator precedence

#### mul binds tighter than add

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("a + b * c")).to_equal("Add(Id(a), Mul(Id(b), Id(c)))")
```

</details>

#### power binds tighter than mul

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("a * b^c")).to_equal("Mul(Id(a), Pow(Id(b), Id(c)))")
```

</details>

#### negation applies to power

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("-x^2")).to_equal("Neg(Pow(Id(x), Num(2)))")
```

</details>

#### implicit multiplication

#### number followed by identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("3x")).to_equal("Mul(Num(3), Id(x))")
```

</details>

#### number followed by paren group

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("2(x)")).to_equal("Mul(Num(2), Group(Id(x)))")
```

</details>

#### identifier followed by paren starts function call

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("f(x)")).to_equal("Call(f, Id(x))")
```

</details>

#### nested grouping

#### handles nested parentheses

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_debug("((x))")).to_equal("Group(Group(Id(x)))")
```

</details>

#### chained postfix

#### handles subscript then transpose

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("A[i]'")
expect(result).to_contain("Transpose")
expect(result).to_contain("Sub")
```

</details>

#### known function detection for latex

#### recognizes sin as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("sin(x)")
expect(result).to_contain("\\sin")
```

</details>

#### recognizes cos as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("cos(x)")
expect(result).to_contain("\\cos")
```

</details>

#### recognizes tan as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("tan(x)")
expect(result).to_contain("\\tan")
```

</details>

#### recognizes log as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("log(x)")
expect(result).to_contain("\\log")
```

</details>

#### recognizes ln as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("ln(x)")
expect(result).to_contain("\\ln")
```

</details>

#### recognizes exp as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("exp(x)")
expect(result).to_contain("\\exp")
```

</details>

#### recognizes min as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("min(a, b)")
expect(result).to_contain("\\min")
```

</details>

#### recognizes lim as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("lim(x)")
expect(result).to_contain("\\lim")
```

</details>

#### recognizes tanh as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("tanh(x)")
expect(result).to_contain("\\tanh")
```

</details>

#### recognizes sinh as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("sinh(x)")
expect(result).to_contain("\\sinh")
```

</details>

#### recognizes cosh as known

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("cosh(x)")
expect(result).to_contain("\\cosh")
```

</details>

#### treats unknown function as operatorname

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_latex_raw("foo(x)")
expect(result).to_contain('\operatorname{foo}')
```

</details>

#### zero-arg function call

#### renders function with no args

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_text("f()")).to_equal("f()")
```

</details>

#### single dot token

#### handles single dot at end of input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("x.")
expect(result).to_contain("x")
```

</details>

#### character coverage for _is_digit

#### exercises all digit branches 0-9

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Number containing all 10 digits covers every _is_digit branch
val result = to_text("1234567890")
expect(result).to_equal("1234567890")
```

</details>

#### exercises decimal number with dot

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_text("3.14159")
expect(result).to_equal("3.14159")
```

</details>

#### character coverage for _is_alpha

#### exercises lowercase a-m in identifiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = to_text("abcdefg")
expect(r1).to_equal("abcdefg")
val r2 = to_text("hijklm")
expect(r2).to_equal("hijklm")
```

</details>

#### exercises lowercase n-z in identifiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = to_text("nopqr")
expect(r1).to_equal("nopqr")
val r2 = to_text("stuvwxyz")
expect(r2).to_equal("stuvwxyz")
```

</details>

#### exercises uppercase A-M in identifiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = to_text("ABCDEFG")
expect(r1).to_equal("ABCDEFG")
val r2 = to_text("HIJKLM")
expect(r2).to_equal("HIJKLM")
```

</details>

#### exercises uppercase N-Z in identifiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = to_text("NOPQR")
expect(r1).to_equal("NOPQR")
val r2 = to_text("STUVWXYZ")
expect(r2).to_equal("STUVWXYZ")
```

</details>

#### exercises underscore in identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Underscore is alpha in math tokenizer; tokenizes as single ident
val result = to_text("a_b")
expect(result).to_contain("a")
```

</details>

#### _can_start_expr and _can_implicit_mul edge cases

#### no implicit mul after operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After +, next token is num - not implicit mul context
val result = to_debug("a + 2")
expect(result).to_equal("Add(Id(a), Num(2))")
```

</details>

#### implicit mul with num before lparen

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = to_debug("3(a + b)")
expect(result).to_contain("Mul")
expect(result).to_contain("Group")
```

</details>

#### tokenizer number-dot boundary

#### handles number followed by dot-dot range

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Total scenarios | 136 |
| Active scenarios | 136 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
