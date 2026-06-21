# Editor Settings View Specification

> <details>

<!-- sdn-diagram:id=editor_settings_view_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_settings_view_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_settings_view_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_settings_view_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Settings View Specification

## Scenarios

### SettingsViewState class

#### defines SettingsViewState with all required fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/settings_view.spl")
expect(src.contains("class SettingsViewState:")).to_equal(true)
expect(src.contains("schema:")).to_equal(true)
expect(src.contains("filtered:")).to_equal(true)
expect(src.contains("selected_index:")).to_equal(true)
expect(src.contains("category_index:")).to_equal(true)
expect(src.contains("categories:")).to_equal(true)
expect(src.contains("search_query:")).to_equal(true)
expect(src.contains("editing:")).to_equal(true)
expect(src.contains("edit_value:")).to_equal(true)
```

</details>

#### defines required methods on SettingsViewState

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/settings_view.spl")
expect(src.contains("static fn new(")).to_equal(true)
expect(src.contains("me select_next()")).to_equal(true)
expect(src.contains("me select_prev()")).to_equal(true)
expect(src.contains("me next_category()")).to_equal(true)
expect(src.contains("me prev_category()")).to_equal(true)
expect(src.contains("me apply_filter()")).to_equal(true)
expect(src.contains("me start_edit(")).to_equal(true)
expect(src.contains("me cancel_edit()")).to_equal(true)
expect(src.contains("fn current_setting()")).to_equal(true)
```

</details>

### EditorController settings integration

#### has settings_view and config fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_controller.spl")
expect(src.contains("settings_view:")).to_equal(true)
expect(src.contains("config:")).to_equal(true)
```

</details>

#### has settings_open and settings_close methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_controller.spl")
expect(src.contains("me settings_open()")).to_equal(true)
expect(src.contains("me settings_close()")).to_equal(true)
```

</details>

#### has _dispatch_settings_key method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_controller.spl")
expect(src.contains("me _dispatch_settings_key(")).to_equal(true)
```

</details>

#### handle_key dispatches to settings when settings_view is active

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_ctrl_core.spl")
expect(src.contains("if ctrl.settings_view != nil:")).to_equal(true)
expect(src.contains("return ctrl_dispatch_settings_key(ctrl, key)")).to_equal(true)
```

</details>

#### _dispatch_command_key handles settings parsed command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_ctrl_core.spl")
expect(src.contains("parsed.name == \"settings\"")).to_equal(true)
expect(src.contains("ctrl_settings_open(ctrl)")).to_equal(true)
```

</details>

### TUI settings rendering

#### _tui_render_settings exists in tui_shell.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/tui_shell_panels.spl")
expect(src.contains("fn _tui_render_settings(")).to_equal(true)
```

</details>

#### tui_render_frame checks settings_view before editor rendering

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/tui_shell.spl")
expect(src.contains("if ctrl.settings_view != nil:")).to_equal(true)
expect(src.contains("_tui_render_settings(ctrl, zones)")).to_equal(true)
```

</details>

### commands.spl settings command

#### parses settings command from commandline

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"settings\"")).to_equal(true)
expect(src.contains("editor_cmd(\"settings\")")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_settings_view_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SettingsViewState class
- EditorController settings integration
- TUI settings rendering
- commands.spl settings command

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
