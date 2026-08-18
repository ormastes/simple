# chart_embed_spec

> Chart-embedded-on-a-slide spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# chart_embed_spec

Chart-embedded-on-a-slide spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/slides/chart_embed_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Chart-embedded-on-a-slide spec.

Verifies the `app.office.slides.chart_embed` model: a chart (bar/column/pie)
embedded as a positioned graphic frame on a slide. Covers the rendered
per-point bars (hand-computed pct-of-max / pct-of-total), the SVG rendering
(rect count + title), the pptx `<p:graphicFrame>` fragment, and the point
count.

## Scenarios

### chart_embed: rendered bars

#### computes pct-of-max for a column chart (max=30)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val series = series_new(["Q1", "Q2", "Q3"], ["10", "30", "20"])
val chart = embed_new("column", 100, 100, 400, 300, "Sales", series)
val bars = chart_bars(chart)
expect(bars).to_equal(["Q1:10:33", "Q2:30:100", "Q3:20:66"])
```

</details>

#### computes pct-of-total for a pie chart (total=60)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val series = series_new(["Q1", "Q2", "Q3"], ["10", "30", "20"])
val chart = embed_new("pie", 100, 100, 400, 300, "Sales", series)
val bars = chart_bars(chart)
expect(bars).to_equal(["Q1:10:16", "Q2:30:50", "Q3:20:33"])
```

</details>

### chart_embed: SVG rendering
_A column chart embed renders one rect per data point plus the title._

#### renders an <svg> with 3 rects and the title Sales

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val series = series_new(["Q1", "Q2", "Q3"], ["10", "30", "20"])
val chart = embed_new("column", 100, 100, 400, 300, "Sales", series)
val svg = chart_to_svg(chart)
expect(svg).to_contain("<svg")
expect(svg).to_contain("Sales")
val rect_count = svg.split("<rect").len() - 1
expect(rect_count).to_equal(3)
```

</details>

### chart_embed: pptx graphic frame

#### emits a graphicFrame with the x/y offset and a c:chart child

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val series = series_new(["Q1", "Q2", "Q3"], ["10", "30", "20"])
val chart = embed_new("column", 100, 100, 400, 300, "Sales", series)
val xml = embed_to_pptx_xml(chart)
expect(xml).to_contain("<p:graphicFrame")
expect(xml).to_contain("x=\"100\"")
expect(xml).to_contain("y=\"100\"")
expect(xml).to_contain("<c:chart")
```

</details>

### chart_embed: point count
_chart_point_count() reports the number of data points in the series._

#### reports 3 points for the Q1/Q2/Q3 series

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val series = series_new(["Q1", "Q2", "Q3"], ["10", "30", "20"])
val chart = embed_new("column", 100, 100, 400, 300, "Sales", series)
expect(chart_point_count(chart)).to_equal(3)
```

</details>

### deliberate-fail probe (fixed to green)

#### has exactly 3 points, not 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val series = series_new(["Q1", "Q2", "Q3"], ["10", "30", "20"])
val chart = embed_new("column", 100, 100, 400, 300, "Sales", series)
expect(chart_point_count(chart)).to_equal(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
