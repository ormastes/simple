# Editor Tui Polish Specification

> Tests covering GUI drag state — struct, GUI drag handlers — functions, TUI split border rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Tui Polish Specification

## Scenarios

### GUI drag state — struct

#### defines DragState with active, source_panel_id, source_zone

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines DragState with active, source_panel_id, source_zone
   - Expected: src contains `struct DragState:`
   - Expected: src contains `active: bool`
   - Expected: src contains `source_panel_id: text`
   - Expected: src contains `source_zone: i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines DragState with active, source_panel_id, source_zone")
val src = read_text("src/app/editor/gui_shell_core.spl")
expect(src.contains("struct DragState:")).to_equal(true)
expect(src.contains("active: bool")).to_equal(true)
expect(src.contains("source_panel_id: text")).to_equal(true)
expect(src.contains("source_zone: i64")).to_equal(true)
```

</details>

#### defines DragState with mouse_x, mouse_y, drop_target_zone

- defines DragState with mouse_x, mouse_y, drop_target_zone
   - Expected: src contains `mouse_x: i64`
   - Expected: src contains `mouse_y: i64`
   - Expected: src contains `drop_target_zone: i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines DragState with mouse_x, mouse_y, drop_target_zone")
val src = read_text("src/app/editor/gui_shell_core.spl")
expect(src.contains("mouse_x: i64")).to_equal(true)
expect(src.contains("mouse_y: i64")).to_equal(true)
expect(src.contains("drop_target_zone: i64")).to_equal(true)
```

</details>

### GUI drag handlers — functions

#### has gui_handle_mouse_down

- has gui_handle_mouse_down
   - Expected: src contains `fn gui_handle_mouse_down(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has gui_handle_mouse_down")
val src = read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("fn gui_handle_mouse_down(")).to_equal(true)
```

</details>

#### has gui_handle_mouse_move

- has gui_handle_mouse_move
   - Expected: src contains `fn gui_handle_mouse_move(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has gui_handle_mouse_move")
val src = read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("fn gui_handle_mouse_move(")).to_equal(true)
```

</details>

#### has gui_handle_mouse_up

- has gui_handle_mouse_up
   - Expected: src contains `fn gui_handle_mouse_up(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has gui_handle_mouse_up")
val src = read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("fn gui_handle_mouse_up(")).to_equal(true)
```

</details>

#### has gui_compute_drop_zone

- has gui_compute_drop_zone
   - Expected: src contains `fn gui_compute_drop_zone(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has gui_compute_drop_zone")
val src = read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("fn gui_compute_drop_zone(")).to_equal(true)
```

</details>

#### has gui_render_drop_overlay

- has gui_render_drop_overlay
   - Expected: src contains `fn gui_render_drop_overlay(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has gui_render_drop_overlay")
val src = read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("fn gui_render_drop_overlay(")).to_equal(true)
```

</details>

### TUI split border rendering

#### has _tui_render_split_borders function

- has _tui_render_split_borders function
   - Expected: src contains `fn _tui_render_split_borders(`
   - Expected: src contains `fn _tui_render_vertical_split_border(`
   - Expected: src contains `fn _tui_render_horizontal_split_border(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has _tui_render_split_borders function")
val src = read_text("src/app/editor/tui_shell_panels.spl")
expect(src.contains("fn _tui_render_split_borders(")).to_equal(true)
expect(src.contains("fn _tui_render_vertical_split_border(")).to_equal(true)
expect(src.contains("fn _tui_render_horizontal_split_border(")).to_equal(true)
```

</details>

#### has _tui_render_pane_tabs function

- has _tui_render_pane_tabs function
   - Expected: src contains `fn _tui_render_pane_tabs(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has _tui_render_pane_tabs function")
val src = read_text("src/app/editor/tui_shell_panels.spl")
expect(src.contains("fn _tui_render_pane_tabs(")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_tui_polish_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GUI drag state — struct, GUI drag handlers — functions, TUI split border rendering.
- GUI drag state — struct
- GUI drag handlers — functions
- TUI split border rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8cbb6ca57667bf0ade7e7c682c0d74391d318b922b1a40f050f2f4268b7d4e37`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8cbb6ca57667bf0ade7e7c682c0d74391d318b922b1a40f050f2f4268b7d4e37`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8cbb6ca57667bf0ade7e7c682c0d74391d318b922b1a40f050f2f4268b7d4e37`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/editor_tui_polish_spec.spl
mirror: doc/06_spec/03_system/gui/editor_tui_polish_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_tui_polish_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_tui_polish_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_tui_polish_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines DragState with active, source_panel_id, source_zone' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_tui_polish_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines DragState with mouse_x, mouse_y, drop_target_zone' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_tui_polish_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has gui_handle_mouse_down' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
