# Vector Shapes Specification

> _Shapes accumulate on a canvas._

<!-- sdn-diagram:id=vector_shapes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vector_shapes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vector_shapes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vector_shapes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vector Shapes Specification

## Scenarios

### vector draw: canvas shape model
_Shapes accumulate on a canvas._

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = empty_canvas(200, 100)
expect(canvas_shape_count(c)).to_equal(0)
```

</details>

#### accumulates added shapes

- var c = empty canvas
- c = add shape
- c = add shape
   - Expected: canvas_shape_count(c) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = empty_canvas(200, 100)
c = add_shape(c, DrawShape.Rect(x: 10, y: 20, w: 50, h: 30, fill: "red"))
c = add_shape(c, DrawShape.Circle(cx: 100, cy: 50, r: 25, fill: "blue"))
expect(canvas_shape_count(c)).to_equal(2)
```

</details>

### vector draw: SVG rendering
_Shapes render to well-formed SVG elements._

#### wraps the canvas in an svg root

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = empty_canvas(200, 100)
val svg = canvas_to_svg(c)
expect(svg).to_start_with("<svg ")
expect(svg).to_end_with("</svg>")
```

</details>

#### renders a rect element with its fill

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svg = shape_to_svg(DrawShape.Rect(x: 10, y: 20, w: 50, h: 30, fill: "red"))
expect(svg).to_start_with("<rect ")
expect(svg).to_contain("fill=\"red\"")
```

</details>

#### renders a circle element with its fill

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svg = shape_to_svg(DrawShape.Circle(cx: 100, cy: 50, r: 25, fill: "blue"))
expect(svg).to_start_with("<circle ")
expect(svg).to_contain("fill=\"blue\"")
```

</details>

#### renders a label with its content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svg = shape_to_svg(DrawShape.Label(x: 5, y: 90, content: "Hi"))
expect(svg).to_contain(">Hi</text>")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/drawing/vector_shapes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- vector draw: canvas shape model
- vector draw: SVG rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
