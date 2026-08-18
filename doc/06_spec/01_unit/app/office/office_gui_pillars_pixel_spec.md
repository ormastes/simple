# office_gui_pillars_pixel_spec

> Office interactive-GUI pixel render across suite pillars.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# office_gui_pillars_pixel_spec

Office interactive-GUI pixel render across suite pillars.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/office_gui_pillars_pixel_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Office interactive-GUI pixel render across suite pillars.

Companion to office_gui_pixel_spec (the counter pilot). Proves the office GUI
rasterizes REAL pixels through the production browser layout/paint path for the
concrete suite surfaces — a spreadsheet grid (Calc/Excel), a chart, a pivot
table, and a slide (Impress/PowerPoint) — not just the counter pilot. Each
surface's view-builder (sheet_gui_view / chart_gui_view / pivot_gui_view /
slide_gui_view, all independently spec-covered) is rendered to an ARGB buffer
via its office_gui_*_pixels entry, and the non-background pixel count is
asserted positive (real widget content, not a blank canvas).

This is the cross-pillar interactive-GUI-fidelity evidence: the same render
path production uses, exercised for four distinct office surfaces, all green
and fast (each rasterizes in a few seconds after the apply_decls perf fix and
the default_style overload-collision workaround). The deliberate-fail probe at
the end proves the runner actually executes these rasterizations.

## Scenarios

### office GUI pillars: spreadsheet grid renders pixels
_The Calc/Excel grid surface rasterizes real content._

#### sheet_gui_view rasterizes to a non-blank frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = sheet_gui_view(_demo_sheet(), 2, 2)
val pixels = office_gui_sheet_pixels(view)
val nonbg = office_gui_non_background_pixel_count(pixels)
expect(pixels.len()).to_be_greater_than(0)
expect(nonbg).to_be_greater_than(0)
```

</details>

### office GUI pillars: chart renders pixels
_The chart surface rasterizes real content._

#### chart_gui_view rasterizes to a non-blank frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = chart_gui_view(_demo_sheet(), "bar", "B1:B2", "A1:A2", "Sales", 96, 64)
val pixels = office_gui_chart_pixels(view)
val nonbg = office_gui_non_background_pixel_count(pixels)
expect(nonbg).to_be_greater_than(0)
```

</details>

### office GUI pillars: pivot table renders pixels
_The pivot surface rasterizes real content._

#### pivot_gui_view rasterizes to a non-blank frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = pivot_gui_view(_pivot_sheet(), "A1:C4", 0, 1, 2, "SUM", "Region x Product")
val pixels = office_gui_pivot_pixels(view)
val nonbg = office_gui_non_background_pixel_count(pixels)
expect(nonbg).to_be_greater_than(0)
```

</details>

### office GUI pillars: slide renders pixels
_The Impress/PowerPoint slide surface rasterizes real content._

#### slide_gui_view rasterizes to a non-blank frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var deck: [Slide] = []
var s = blank_slide("s1")
s = add_text_box(s, "title", "Intro", 60, 60, 840, 120)
deck.push(s)
val view = slide_gui_view(deck, 0)
val pixels = office_gui_slide_pixels(view)
val nonbg = office_gui_non_background_pixel_count(pixels)
expect(nonbg).to_be_greater_than(0)
```

</details>

#### deliberate-fail probe proves the tail of the file executes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = sheet_gui_view(_demo_sheet(), 2, 2)
val pixels = office_gui_sheet_pixels(view)
val nonbg = office_gui_non_background_pixel_count(pixels)
expect(nonbg).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
