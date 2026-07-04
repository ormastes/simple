# Editor Tui Polish Specification

> <details>

<!-- sdn-diagram:id=editor_tui_polish_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_tui_polish_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_tui_polish_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_tui_polish_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Tui Polish Specification

## Scenarios

### GUI drag state — struct

#### defines DragState with active, source_panel_id, source_zone

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_core.spl")
expect(src.contains("struct DragState:")).to_equal(true)
expect(src.contains("active: bool")).to_equal(true)
expect(src.contains("source_panel_id: text")).to_equal(true)
expect(src.contains("source_zone: i64")).to_equal(true)
```

</details>

#### defines DragState with mouse_x, mouse_y, drop_target_zone

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_core.spl")
expect(src.contains("mouse_x: i64")).to_equal(true)
expect(src.contains("mouse_y: i64")).to_equal(true)
expect(src.contains("drop_target_zone: i64")).to_equal(true)
```

</details>

### GUI drag handlers — functions

#### has gui_handle_mouse_down

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("fn gui_handle_mouse_down(")).to_equal(true)
```

</details>

#### has gui_handle_mouse_move

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("fn gui_handle_mouse_move(")).to_equal(true)
```

</details>

#### has gui_handle_mouse_up

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("fn gui_handle_mouse_up(")).to_equal(true)
```

</details>

#### has gui_compute_drop_zone

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("fn gui_compute_drop_zone(")).to_equal(true)
```

</details>

#### has gui_render_drop_overlay

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("fn gui_render_drop_overlay(")).to_equal(true)
```

</details>

### TUI split border rendering

#### has _tui_render_split_borders function

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/tui_shell_panels.spl")
expect(src.contains("fn _tui_render_split_borders(")).to_equal(true)
expect(src.contains("fn _tui_render_vertical_split_border(")).to_equal(true)
expect(src.contains("fn _tui_render_horizontal_split_border(")).to_equal(true)
```

</details>

#### has _tui_render_pane_tabs function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
