# math_editor_spec

> Verifies the Math component: expressions render to MathML with escaped tokens, precedence-aware grouping for core operators, and structured superscript, fraction, subscript, fenced group, and square-root helpers. The renderer is the display core of an equation editor.

<!-- sdn-diagram:id=math_editor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_editor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_editor_spec -> std
math_editor_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_editor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# math_editor_spec

Verifies the Math component: expressions render to MathML with escaped tokens, precedence-aware grouping for core operators, and structured superscript, fraction, subscript, fenced group, and square-root helpers. The renderer is the display core of an equation editor.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/math_editor.md |
| Plan | doc/03_plan/sys_test/math_editor.md |
| Design | doc/07_guide/app/ide_office_plugin_suite.md |
| Research | N/A |
| Source | `test/01_unit/app/office/math_editor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the Math component: expressions render to MathML with escaped tokens,
precedence-aware grouping for core operators, and structured superscript,
fraction, subscript, fenced group, and square-root helpers. The renderer is the
display core of an equation editor.

## Examples

`math_to_mathml("frac(1, 2)")` renders a MathML `<mfrac>`.
`math_to_mathml("a + b * c")` preserves multiplication as a nested right-hand
group. `math_to_mathml_checked("a +")` rejects malformed input while returning
flat fallback MathML. `math_fraction("x + 1", "y")` and `math_fenced("(", "x +
y", ")")` produce nested MathML rows for equation editor layout.

**Requirements:** doc/02_requirements/feature/math_editor.md
**NFR:** doc/02_requirements/nfr/math_editor.md
**Plan:** doc/03_plan/sys_test/math_editor.md
**Design:** doc/07_guide/app/ide_office_plugin_suite.md
**Research:** N/A

## Scenarios

### Math editor: flat expression to MathML
_A flat expression renders to a MathML <math><mrow> sequence._

#### wraps output in a MathML math/mrow root

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_to_mathml("a + 1")
expect(ml).to_start_with("<math ")
expect(ml).to_contain("<mrow>")
expect(ml).to_end_with("</math>")
```

</details>

#### renders an identifier as <mi>

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_to_mathml("a + 1")
expect(ml).to_contain("<mi>a</mi>")
```

</details>

#### renders a multi-digit number as <mn>

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_to_mathml("x + 12")
expect(ml).to_contain("<mn>12</mn>")
```

</details>

#### renders an operator as <mo>

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_to_mathml("a + b")
expect(ml).to_contain("<mo>+</mo>")
```

</details>

#### escapes XML-sensitive operators

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_to_mathml("a < b & c")
expect(ml).to_contain("<mo>&lt;</mo>")
expect(ml).to_contain("<mo>&amp;</mo>")
```

</details>

### Math editor: precedence parser
_Core operators render with deterministic precedence-aware grouping._

#### reports empty checked input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_to_mathml_checked("   ")
expect(result.accepted).to_be(false)
expect(result.reason).to_equal("empty-expression")
```

</details>

#### reports token-limit checked input with flat fallback MathML

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var expr = "x"
var i = 0
while i < 193:
    expr = expr + " + x"
    i = i + 1
val result = math_to_mathml_checked(expr)
expect(result.accepted).to_be(false)
expect(result.reason).to_equal("token-limit")
expect(result.mathml).to_contain("<mi>x</mi>")
```

</details>

#### groups multiplication tighter than addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_to_mathml("a + b * c")
expect(ml).to_contain("<mi>a</mi><mo>+</mo><mrow><mi>b</mi><mo>*</mo><mi>c</mi></mrow>")
```

</details>

#### respects parenthesized groups before multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_to_mathml("(a + b) * c")
expect(ml).to_contain("<mrow><mi>a</mi><mo>+</mo><mi>b</mi></mrow><mo>*</mo><mi>c</mi>")
```

</details>

#### renders slash as a MathML fraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_to_mathml("a / b")
expect(ml).to_contain("<mfrac><mi>a</mi><mi>b</mi></mfrac>")
```

</details>

#### keeps same-precedence subtraction left associative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_to_mathml("a - b - c")
expect(ml).to_contain("<mrow><mi>a</mi><mo>-</mo><mi>b</mi></mrow><mo>-</mo><mi>c</mi>")
```

</details>

#### keeps multiplication and division in one left-associative precedence tier

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_to_mathml("a * b / c")
expect(ml).to_contain("<mfrac><mrow><mi>a</mi><mo>*</mo><mi>b</mi></mrow><mi>c</mi></mfrac>")
```

</details>

#### renders caret as a MathML superscript

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_to_mathml("x ^ 2")
expect(ml).to_contain("<msup><mi>x</mi><mn>2</mn></msup>")
```

</details>

#### renders unary minus as an operator row

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_to_mathml("-x")
expect(ml).to_contain("<mrow><mo>-</mo><mi>x</mi></mrow>")
```

</details>

#### renders sqrt function shorthand

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_to_mathml("sqrt(x + 1)")
expect(ml).to_contain("<msqrt><mrow><mi>x</mi><mo>+</mo><mn>1</mn></mrow></msqrt>")
```

</details>

#### reports malformed checked input with flat fallback MathML

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_to_mathml_checked("a + (b")
expect(result.accepted).to_be(false)
expect(result.reason).to_equal("unbalanced-parentheses")
expect(result.mathml).to_contain("<mi>a</mi>")
expect(result.mathml).to_contain("<mo>(</mo>")
```

</details>

#### reports checked syntax errors with flat fallback MathML

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_to_mathml_checked("a +")
expect(result.accepted).to_be(false)
expect(result.reason).to_equal("syntax-error")
expect(result.mathml).to_contain("<mi>a</mi>")
expect(result.mathml).to_contain("<mo>+</mo>")
```

</details>

#### reports malformed fraction arity in checked rendering

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing = math_to_mathml_checked("frac(1)")
val extra = math_to_mathml_checked("frac(1, 2, 3)")
expect(missing.accepted).to_be(false)
expect(missing.reason).to_equal("frac-arity")
expect(extra.accepted).to_be(false)
expect(extra.reason).to_equal("frac-arity")
```

</details>

#### reports empty fraction operands in checked rendering

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_numerator = math_to_mathml_checked("frac(, 2)")
val missing_denominator = math_to_mathml_checked("frac(1,)")
expect(missing_numerator.accepted).to_be(false)
expect(missing_numerator.reason).to_equal("missing-argument")
expect(missing_denominator.accepted).to_be(false)
expect(missing_denominator.reason).to_equal("missing-argument")
```

</details>

#### reports missing sqrt arguments in checked rendering

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_to_mathml_checked("sqrt()")
expect(result.accepted).to_be(false)
expect(result.reason).to_equal("missing-argument")
```

</details>

#### reports malformed nested checked expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_operator = math_to_mathml_checked("a + * b")
val bad_fraction = math_to_mathml_checked("a + frac(1)")
val bad_root = math_to_mathml_checked("a + sqrt()")
expect(bad_operator.accepted).to_be(false)
expect(bad_operator.reason).to_equal("syntax-error")
expect(bad_fraction.accepted).to_be(false)
expect(bad_fraction.reason).to_equal("frac-arity")
expect(bad_root.accepted).to_be(false)
expect(bad_root.reason).to_equal("missing-argument")
```

</details>

### Math editor: structured forms
_Fractions, scripts, roots, and fenced groups produce structured MathML._

#### renders fraction shorthand through the public MathML renderer

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_to_mathml("frac(1, 2)")
expect(ml).to_contain("<mfrac>")
expect(ml).to_contain("<mn>1</mn>")
expect(ml).to_contain("<mn>2</mn>")
```

</details>

#### renders fraction shorthand rows for compound numerator expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_to_mathml("frac(x + 1, y)")
expect(ml).to_contain("<mfrac><mrow><mi>x</mi><mo>+</mo><mn>1</mn></mrow><mi>y</mi></mfrac>")
```

</details>

#### renders fraction shorthand with precedence inside arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_to_mathml("frac(a + b * c, d)")
expect(ml).to_contain("<mfrac><mrow><mi>a</mi><mo>+</mo><mrow><mi>b</mi><mo>*</mo><mi>c</mi></mrow></mrow><mi>d</mi></mfrac>")
```

</details>

#### renders multiple fraction shorthands as a normal expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_to_mathml_checked("frac(1, 2) + frac(3, 4)")
expect(result.accepted).to_be(true)
expect(result.mathml).to_contain("<mfrac><mn>1</mn><mn>2</mn></mfrac>")
expect(result.mathml).to_contain("<mo>+</mo>")
expect(result.mathml).to_contain("<mfrac><mn>3</mn><mn>4</mn></mfrac>")
```

</details>

#### falls back to flat rendering for malformed fraction shorthand

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_to_mathml("frac(1)")
expect(ml).to_contain("<mi>frac</mi>")
expect(ml).to_contain("<mn>1</mn>")
```

</details>

#### renders explicit fractions with mfrac

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_fraction("x + 1", "y")
expect(ml).to_start_with("<mfrac>")
expect(ml).to_contain("<mrow><mi>x</mi><mo>+</mo><mn>1</mn></mrow>")
expect(ml).to_contain("<mi>y</mi>")
```

</details>

#### renders a superscript with msup

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_superscript("x", "2")
expect(ml).to_start_with("<msup>")
expect(ml).to_contain("<mi>x</mi>")
expect(ml).to_contain("<mn>2</mn>")
```

</details>

#### renders a subscript with msub

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_subscript("x", "i")
expect(ml).to_start_with("<msub>")
expect(ml).to_contain("<mi>x</mi>")
expect(ml).to_contain("<mi>i</mi>")
```

</details>

#### renders a square root with msqrt

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_sqrt("y")
expect(ml).to_start_with("<msqrt>")
expect(ml).to_contain("<mi>y</mi>")
```

</details>

#### renders fenced expression groups

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ml = math_fenced("(", "x + y", ")")
expect(ml).to_start_with("<mrow>")
expect(ml).to_contain("<mo>(</mo>")
expect(ml).to_contain("<mi>x</mi><mo>+</mo><mi>y</mi>")
expect(ml).to_contain("<mo>)</mo>")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/math_editor.md](doc/02_requirements/feature/math_editor.md)
- **Plan:** [doc/03_plan/sys_test/math_editor.md](doc/03_plan/sys_test/math_editor.md)
- **Design:** [doc/07_guide/app/ide_office_plugin_suite.md](doc/07_guide/app/ide_office_plugin_suite.md)


</details>
