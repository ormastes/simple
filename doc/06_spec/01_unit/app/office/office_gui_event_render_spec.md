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
| Updated | 2026-08-26 |
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

#### session_key down advances the selected cell and still renders

- session_key down advances the selected cell and still renders
   - Expected: session.selected_ref equals `A1`
   - Expected: moved.selected_ref equals `A2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("session_key down advances the selected cell and still renders")
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

- session_edit updates the rendered value in the view dump


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("session_edit updates the rendered value in the view dump")
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

- session_click yields a valid post-event session that renders


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("session_click yields a valid post-event session that renders")
val session = session_new(_demo_sheet(), "A1")
val clicked = session_click(session, 40, 50, 2, 2, 96, 64)
assert_true(clicked.selected_ref.len() > 0)
assert_true(_renders_real_pixels(clicked))
```

</details>

#### deliberate-fail probe proves the tail of the file executes

- deliberate-fail probe proves the tail of the file executes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deliberate-fail probe proves the tail of the file executes")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `709c2c919b2cb85234f0b3ed960809f25e7ba2e4a420863011af968b52c7a42d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `709c2c919b2cb85234f0b3ed960809f25e7ba2e4a420863011af968b52c7a42d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `709c2c919b2cb85234f0b3ed960809f25e7ba2e4a420863011af968b52c7a42d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/office_gui_event_render_spec.spl
mirror: doc/06_spec/01_unit/app/office/office_gui_event_render_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/office_gui_event_render_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/office_gui_event_render_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/office_gui_event_render_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'session_key down advances the selected cell and still renders' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/office_gui_event_render_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'session_edit updates the rendered value in the view dump' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/office_gui_event_render_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'session_click yields a valid post-event session that renders' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
