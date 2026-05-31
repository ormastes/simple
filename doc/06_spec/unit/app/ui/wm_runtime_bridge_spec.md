# Wm Runtime Bridge Specification

## Scenarios

### host web WM runtime bridge

#### maps host pointer hits on taskbar pins to launcher commands

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = host_wm_pointer_runtime_command(_scene(), _taskbar(), 70, 575, "left", "down", 1000, "09:41", 2)
expect(command.kind).to_equal("launcher_launch")
expect(command.app_id).to_equal("browser")
expect(command.handled).to_equal(true)
```

</details>

#### maps host pointer hits on running taskbar entries to focus commands

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = host_wm_pointer_runtime_command(_scene(), _taskbar(), 120, 575, "left", "down", 1000, "09:41", 2)
expect(command.kind).to_equal("window_focus")
expect(command.window_id).to_equal("win1")
expect(command.app_id).to_equal("demo.app")
```

</details>

#### maps host pointer hits on titlebars and command lane icons

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drag = host_wm_pointer_runtime_command(_scene(), _taskbar(), 90, 125, "left", "down", 1000, "09:41", 2)
val icon_wire = host_wm_pointer_runtime_wire(_scene(), _taskbar(), 780, 8, "left", "down", 1000, "09:41", 2)

expect(drag.kind).to_equal("window_drag_begin")
expect(drag.target_id).to_equal("surf2")
expect(icon_wire).to_contain("kind=command_lane_icon")
expect(icon_wire).to_contain("target=right_icon_1")
```

</details>

#### keeps non-left or non-down host pointer events ignored

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = host_wm_pointer_runtime_command(_scene(), _taskbar(), 70, 575, "right", "down", 1000, "09:41", 2)
expect(command.kind).to_equal("ignored")
expect(command.handled).to_equal(false)
```

</details>

<details>
<summary>Advanced: applies host event-loop pointer steps to shared shell state</summary>

#### applies host event-loop pointer steps to shared shell state

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val launched = host_wm_apply_pointer(wm_runtime_shell_state_empty(), _scene(), _taskbar(), 70, 575, "left", "down", 1000, "09:41", 2)
val focused = host_wm_apply_pointer(launched, _scene(), _taskbar(), 120, 575, "left", "down", 1000, "09:41", 2)
val marker = host_wm_event_loop_marker(_scene(), _taskbar(), 90, 125, "left", "down", 1000, "09:41", 2)

expect(launched.launched_apps.len()).to_equal(1)
expect(launched.launched_apps[0]).to_equal("browser")
expect(focused.focused_window_id).to_equal("win1")
expect(marker).to_contain("[host-wm] loop-step command=window_drag_begin")
expect(marker).to_contain("target=surf2")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/wm_runtime_bridge_spec.spl` |
| Updated | 2026-05-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- host web WM runtime bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

