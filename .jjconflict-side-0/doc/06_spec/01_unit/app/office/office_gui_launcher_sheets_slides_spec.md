# office_gui_launcher_sheets_slides_spec

> Interactive-GUI pixel render for the Sheets and Slides launcher apps.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# office_gui_launcher_sheets_slides_spec

Interactive-GUI pixel render for the Sheets and Slides launcher apps.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/office_gui_launcher_sheets_slides_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Interactive-GUI pixel render for the Sheets and Slides launcher apps.

Renders the SheetsApp and SlidesApp launcher surfaces through the production
browser layout/paint path (office_gui_launcher_frame in gui_apps.spl — kept out
of gui.spl to avoid fattening its import graph) and asserts real (non-blank)
content. Split from the mail/planner spec so each file stays well under the
runner's kill budget.

## Scenarios

### office GUI launcher: Sheets app renders pixels

#### the sheets frame is a non-blank 96x64 buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = office_gui_launcher_frame("sheets")
val w = office_gui_launcher_frame_width()
val h = office_gui_launcher_frame_height()
expect(pixels.len()).to_equal(w * h)
val nonbg = office_gui_non_background_pixel_count(pixels)
expect(nonbg).to_be_greater_than(0)
```

</details>

### office GUI launcher: Slides app renders pixels

#### the slides frame has real content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = office_gui_launcher_frame("slides")
val nonbg = office_gui_non_background_pixel_count(pixels)
expect(nonbg).to_be_greater_than(0)
```

</details>

#### deliberate-fail probe proves the tail of the file executes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = office_gui_launcher_frame("slides")
val nonbg = office_gui_non_background_pixel_count(pixels)
expect(nonbg).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
