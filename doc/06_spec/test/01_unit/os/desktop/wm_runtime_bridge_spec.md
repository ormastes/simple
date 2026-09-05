# Wm Runtime Bridge Specification

> <details>

<!-- sdn-diagram:id=wm_runtime_bridge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_runtime_bridge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_runtime_bridge_spec -> std
wm_runtime_bridge_spec -> common
wm_runtime_bridge_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_runtime_bridge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Runtime Bridge Specification

## Scenarios

### SimpleOS WM runtime bridge

#### maps framebuffer taskbar pointer hits to launcher commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = simpleos_wm_pointer_runtime_command(_scene(), _taskbar(), 70, 575, "left", "down", 1000, "09:41", 2)
expect(command.kind).to_equal("launcher_launch")
expect(command.app_id).to_equal("browser")
expect(command.handled).to_equal(true)
```

</details>

#### applies running-window focus and titlebar drag state

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val focused = simpleos_wm_apply_pointer(wm_runtime_shell_state_empty(), _scene(), _taskbar(), 120, 575, "left", "down", 1000, "09:41", 2)
val dragging = simpleos_wm_apply_pointer(focused, _scene(), _taskbar(), 90, 125, "left", "down", 1000, "09:41", 2)

expect(focused.focused_window_id).to_equal("win1")
expect(dragging.focused_window_id).to_equal("win2")
expect(dragging.dragging_surface_id).to_equal("surf2")
expect(dragging.last_command_kind).to_equal("window_drag_begin")
```

</details>

#### emits serial-friendly command markers for QEMU capture checks

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val marker = simpleos_wm_pointer_runtime_marker(_scene(), _taskbar(), 780, 8, "left", "down", 1000, "09:41", 2)
expect(marker).to_contain("[simpleos-wm] command=command_lane_icon")
expect(marker).to_contain("target=right_icon_1")
expect(marker).to_contain("handled=true")
```

</details>

<details>
<summary>Advanced: emits event-loop step markers for direct shell-loop invocation</summary>

#### emits event-loop step markers for direct shell-loop invocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val marker = simpleos_wm_event_loop_marker(_scene(), _taskbar(), 120, 575, "left", "down", 1000, "09:41", 2)
expect(marker).to_contain("[simpleos-wm] loop-step command=window_focus")
expect(marker).to_contain("window=win1")
expect(marker).to_contain("handled=true")
```

</details>


</details>

#### keeps unsupported pointer gestures ignored

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = simpleos_wm_pointer_runtime_command(_scene(), _taskbar(), 70, 575, "right", "down", 1000, "09:41", 2)
val state = simpleos_wm_apply_pointer(wm_runtime_shell_state_empty(), _scene(), _taskbar(), 70, 575, "right", "down", 1000, "09:41", 2)

expect(command.kind).to_equal("ignored")
expect(command.handled).to_equal(false)
expect(state.last_command_kind).to_equal("ignored")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/desktop/wm_runtime_bridge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS WM runtime bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
