# slide_outline_spec

Slide outline unit specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/office/slide_outline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Slide outline unit specification.
Validates CSS-like outline styling and per-slide design metadata for presentation views.

## Scenarios

### Slide outline styling

#### builds CSS-like outline text from the existing presentation model

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pres = empty_presentation("Quarterly Review")
val style = slide_outline_style(".deck-outline .item", "#0F766E", "600", "uppercase", "#F59E0B")
val css = slide_outline_style_css(style)
val lines = presentation_outline_text(pres, style)
expect(css).to_contain("text-transform: uppercase")
expect(css).to_contain("border-left-color: #F59E0B")
expect(lines.join("\n")).to_contain("QUARTERLY REVIEW")
```

</details>

#### builds per-slide CSS-like design metadata tied to outline styling

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pres = empty_presentation("Quarterly Review")
val designs = presentation_designs(pres, "#F59E0B", "uppercase")
val css = presentation_design_css(pres, "#F59E0B", "uppercase")
expect(designs.len()).to_equal(1)
expect(designs[0].slide_id).to_equal("slide_0")
expect(css).to_contain(".slide-page-0")
expect(css).to_contain("background:")
expect(css).to_contain("text-transform: uppercase")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

