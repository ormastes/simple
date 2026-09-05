# shapes_spec

> Slide shapes + build-animation spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# shapes_spec

Slide shapes + build-animation spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/slides/shapes_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Slide shapes + build-animation spec.

Verifies the vector shapes model in `app.office.slides.shapes`: SVG rendering
per shape kind (rect/ellipse/arrow/line/textbox), whole-slide SVG assembly in
insertion order, escaping of shape content, and the build-animation summary
which lists only animated shapes in slide order.

## Scenarios

### shapes: SVG rendering
_Individual shape kinds render to their expected SVG element(s)._

#### renders a filled rect with its position and fill hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rect = shape_new("rect", 10, 20, 100, 50, "", "#4472c4", "fade")
val svg = shape_to_svg(rect)
expect(svg).to_contain("<rect")
expect(svg).to_contain("#4472c4")
expect(svg).to_contain("x=\"10\"")
expect(svg).to_contain("y=\"20\"")
```

</details>

#### renders an ellipse with no fill as fill=none

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ellipse = shape_new("ellipse", 0, 0, 40, 20, "", "", "")
val svg = shape_to_svg(ellipse)
expect(svg).to_contain("<ellipse")
expect(svg).to_contain("fill=\"none\"")
```

</details>

#### renders an arrow as a line plus a triangle polygon head

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arrow = shape_new("arrow", 0, 0, 100, 0, "", "#000000", "fly-in")
val svg = shape_to_svg(arrow)
expect(svg).to_contain("<line")
expect(svg).to_contain("<polygon")
```

</details>

#### renders a textbox as a rect plus text

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tb = shape_new("textbox", 5, 5, 80, 30, "Hello", "#ffffff", "")
val svg = shape_to_svg(tb)
expect(svg).to_contain("<rect")
expect(svg).to_contain("<text")
expect(svg).to_contain(">Hello<")
```

</details>

#### escapes shape content so a literal < renders as &lt;

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tb = shape_new("textbox", 0, 0, 10, 10, "<script>", "", "")
val svg = shape_to_svg(tb)
expect(svg).to_contain("&lt;script&gt;")
expect(svg.contains("<script>")).to_equal(false)
```

</details>

### shapes: slide assembly and animation order

#### wraps all shapes in one <svg> in insertion order

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var slide = shape_slide_new("Diagram")
slide = shape_slide_add(slide, shape_new("rect", 0, 0, 10, 10, "", "#4472c4", "fade"))
slide = shape_slide_add(slide, shape_new("ellipse", 20, 20, 10, 10, "", "", ""))
slide = shape_slide_add(slide, shape_new("arrow", 40, 40, 10, 0, "", "", "fly-in"))
val svg = shape_slide_to_svg(slide, 960, 540)
expect(svg).to_contain("<svg")
expect(svg).to_contain("width=\"960\"")
expect(svg).to_contain("height=\"540\"")
val rect_pos = svg.find("<rect")
val ellipse_pos = svg.find("<ellipse")
val arrow_pos = svg.find("<line")
expect(rect_pos < ellipse_pos).to_equal(true)
expect(ellipse_pos < arrow_pos).to_equal(true)
```

</details>

#### returns only animated shapes, skipping the ellipse, in build order

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var slide = shape_slide_new("Diagram")
slide = shape_slide_add(slide, shape_new("rect", 0, 0, 10, 10, "", "#4472c4", "fade"))
slide = shape_slide_add(slide, shape_new("ellipse", 20, 20, 10, 10, "", "", ""))
slide = shape_slide_add(slide, shape_new("arrow", 40, 40, 10, 0, "", "", "fly-in"))
val summary = shape_anim_summary(slide)
expect(summary).to_equal(["rect:fade", "arrow:fly-in"])
```

</details>

### deliberate-fail probe (fixed to green)

#### has exactly two animated shapes in the summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var slide = shape_slide_new("Diagram")
slide = shape_slide_add(slide, shape_new("rect", 0, 0, 10, 10, "", "#4472c4", "fade"))
slide = shape_slide_add(slide, shape_new("ellipse", 20, 20, 10, 10, "", "", ""))
slide = shape_slide_add(slide, shape_new("arrow", 40, 40, 10, 0, "", "", "fly-in"))
val summary = shape_anim_summary(slide)
expect(summary.len()).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
