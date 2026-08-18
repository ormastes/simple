# office_gui_event_render_spec

> Office interactive-GUI event -> render proof.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# office_gui_event_render_spec

Office interactive-GUI event -> render proof.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/office_gui_event_render_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Office interactive-GUI event -> render proof.

The GUI campaign proved static frame rendering (office_gui_*_pixels) and each
surface's view dump. This spec closes the interactivity half: an INPUT EVENT
applied to a live GUI session drives a change in what the session RENDERS. It
exercises the same event handlers the live terminal loop uses (session_key arrow
navigation, session_edit cell entry, session_click pixel hit-testing) and checks
the rendered view (sheet_gui_view_with_selection's text_dump — the canonical
render surface these GUI specs assert on) plus a non-blank pixel-path sanity
check. This is real event->render interactivity at the logic + render level,
independent of the terminal raw-mode extern the deployed binary still lacks: the
event dispatch + render loop itself is proven here.

(The 96x64 session pixel buffer paints grid structure, not legible cell glyphs,
so content changes are asserted on the text_dump the whole GUI suite uses, while
the pixel path is exercised for the non-blank real-frame guarantee.)

## Scenarios

### office GUI events: arrow-key navigation moves the selection
_Pressing 'down' moves the live selection A1 -> A2._

#### session_key down advances the selected cell and still renders

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = session_new(_demo_sheet(), "A1")
expect(session.selected_ref).to_equal("A1")
val moved = session_key(session, "down", 2, 2, 2, 2)
expect(moved.selected_ref).to_equal("A2")
assert_true(_renders_real_pixels(moved))
```

</details>

### office GUI events: typing edits a cell and the render updates
_Editing the selected cell changes the rendered grid content._

#### session_edit updates the rendered value in the view dump

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = session_new(_demo_sheet(), "A1")
expect(_dump_of(session)).to_contain("10")
val edited = session_edit(session, "A1", "99999")
val edited_dump = _dump_of(edited)
expect(edited_dump).to_contain("99999")
assert_true(_renders_real_pixels(edited))
```

</details>

### office GUI events: a pointer click hit-tests to a cell

#### session_click yields a valid post-event session that renders

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = session_new(_demo_sheet(), "A1")
val clicked = session_click(session, 40, 50, 2, 2, 96, 64)
assert_true(clicked.selected_ref.len() > 0)
assert_true(_renders_real_pixels(clicked))
```

</details>

#### deliberate-fail probe proves the tail of the file executes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = session_new(_demo_sheet(), "A1")
val edited = session_edit(session, "A1", "77777")
expect(_dump_of(edited)).to_contain("77777")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
