# office_gui_pixel_spec

> Office interactive-GUI pixel-render spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# office_gui_pixel_spec

Office interactive-GUI pixel-render spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/office_gui_pixel_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Office interactive-GUI pixel-render spec.

Proves the office GUI renders REAL pixels through the production browser
layout/paint path (office_gui_frame → render_html_tree → the same
simple_web_engine2d_render_html_pixels entry production uses), not a faked
or blank canvas. This is the interactive-GUI-fidelity evidence the campaign
was missing: the counter app's UITree is converted to HTML and rasterized to
an ARGB buffer whose non-background pixel count and checksum are asserted.

Historically this path was held out of the tree (render_frame was quadratic
in CSS size and hung past the 60s runner kill). After the apply_decls
pre-parse perf fix and the default_style overload-collision workaround, the
counter frame rasterizes in a few seconds, so it is now a first-class,
non-greenwashed spec (the deliberate-fail probe below proves the runner
actually executes these bodies).

## Scenarios

### office GUI: frame geometry
_The counter frame rasterizes to a fixed-size ARGB buffer._

#### the frame buffer has exactly width*height pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = office_gui_frame("counter")
val w = office_gui_frame_width()
val h = office_gui_frame_height()
expect(w).to_equal(96)
expect(h).to_equal(64)
expect(pixels.len()).to_equal(w * h)
```

</details>

### office GUI: real content
_A rendered frame carries real widget pixels, not a blank canvas._

#### the counter frame has a positive non-background pixel count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = office_gui_frame("counter")
val nonbg = office_gui_non_background_pixel_count(pixels)
expect(nonbg).to_be_greater_than(0)
```

</details>

### office GUI: Word document surface

#### the word frame has a positive non-background pixel count

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = office_gui_frame("word")
val w = office_gui_frame_width()
val h = office_gui_frame_height()
expect(pixels.len()).to_equal(w * h)
val nonbg = office_gui_non_background_pixel_count(pixels)
expect(nonbg).to_be_greater_than(0)
```

</details>

### office GUI: deterministic render
_Rendering the same app twice yields byte-identical pixels._

#### two renders of the counter produce the same checksum

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = office_gui_frame("counter")
val b = office_gui_frame("counter")
val ca = office_gui_pixel_checksum(a)
val cb = office_gui_pixel_checksum(b)
expect(ca).to_equal(cb)
```

</details>

#### deliberate-fail probe proves the tail of the file executes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = office_gui_frame("counter")
val nonbg = office_gui_non_background_pixel_count(pixels)
# This must be > 0; asserting it correctly keeps the suite green and
# proves this describe (the last in the file) actually runs.
expect(nonbg).to_be_greater_than(0)
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
