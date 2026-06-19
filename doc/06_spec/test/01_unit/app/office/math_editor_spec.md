# math_editor_spec

> Verifies the Math component: a simple math expression renders to MathML (identifiers→<mi>, numbers→<mn>, operators→<mo>), with structured superscript fraction, subscript, fenced group, and square-root helpers. The renderer is the display core of an equation editor.

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
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# math_editor_spec

Verifies the Math component: a simple math expression renders to MathML (identifiers→<mi>, numbers→<mn>, operators→<mo>), with structured superscript fraction, subscript, fenced group, and square-root helpers. The renderer is the display core of an equation editor.

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

Verifies the Math component: a simple math expression renders to MathML
(identifiers→<mi>, numbers→<mn>, operators→<mo>), with structured superscript
fraction, subscript, fenced group, and square-root helpers. The renderer is the
display core of an equation editor.

## Examples

`math_to_mathml("frac(1, 2)")` renders a MathML `<mfrac>`. `math_fraction("x +
1", "y")` and `math_fenced("(", "x + y", ")")` produce nested MathML rows for
equation editor layout.

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
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/math_editor.md](doc/02_requirements/feature/math_editor.md)
- **Plan:** [doc/03_plan/sys_test/math_editor.md](doc/03_plan/sys_test/math_editor.md)
- **Design:** [doc/07_guide/app/ide_office_plugin_suite.md](doc/07_guide/app/ide_office_plugin_suite.md)


</details>
