# Math Editor Specification

> _A flat expression renders to a MathML <math><mrow> sequence._

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
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Editor Specification

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

### Math editor: structured forms
_Superscript and square root produce structured MathML._

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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/math_editor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Math editor: flat expression to MathML
- Math editor: structured forms

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
