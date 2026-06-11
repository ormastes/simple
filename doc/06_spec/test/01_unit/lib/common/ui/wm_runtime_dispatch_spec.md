# Wm Runtime Dispatch Specification

> <details>

<!-- sdn-diagram:id=wm_runtime_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_runtime_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_runtime_dispatch_spec -> std
wm_runtime_dispatch_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_runtime_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Runtime Dispatch Specification

## Scenarios

### shared WM runtime dispatch adapter

#### maps taskbar pinned app hits to launcher launch commands

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dispatch = shared_wm_dispatch_pointer(_scene(), _taskbar(), 70, 575, "left", "down", 1000, "09:41", 2)
val command = wm_runtime_command_from_shared_dispatch(dispatch)

expect(command.kind).to_equal("launcher_launch")
expect(command.app_id).to_equal("browser")
expect(command.handled).to_equal(true)
expect(wm_runtime_dispatch_wire(command)).to_contain("kind=launcher_launch")
expect(wm_runtime_dispatch_wire(command)).to_contain("payload=app_id=browser")
```

</details>

#### maps running taskbar hits to window focus commands

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dispatch = shared_wm_dispatch_pointer(_scene(), _taskbar(), 120, 575, "left", "down", 1000, "09:41", 2)
val command = wm_runtime_command_from_shared_dispatch(dispatch)

expect(command.kind).to_equal("window_focus")
expect(command.window_id).to_equal("win1")
expect(command.app_id).to_equal("demo.app")
expect(command.payload).to_contain("window_id=win1")
```

</details>

#### maps titlebar hits to drag-begin commands

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dispatch = shared_wm_dispatch_pointer(_scene(), _taskbar(), 90, 125, "left", "down", 1000, "09:41", 2)
val command = wm_runtime_command_from_shared_dispatch(dispatch)

expect(command.kind).to_equal("window_drag_begin")
expect(command.target_id).to_equal("surf2")
expect(command.window_id).to_equal("win2")
expect(command.payload).to_contain("surface_id=surf2")
```

</details>

#### maps command lane and background hits to runtime commands

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val clock = wm_runtime_command_from_shared_dispatch(shared_wm_dispatch_pointer(_scene(), _taskbar(), 704, 8, "left", "down", 1000, "09:41", 2))
val icon = wm_runtime_command_from_shared_dispatch(shared_wm_dispatch_pointer(_scene(), _taskbar(), 780, 8, "left", "down", 1000, "09:41", 2))
val bg = wm_runtime_command_from_shared_dispatch(shared_wm_dispatch_pointer(_scene(), _taskbar(), 780, 300, "left", "down", 1000, "09:41", 2))

expect(clock.kind).to_equal("command_lane_clock")
expect(icon.kind).to_equal("command_lane_icon")
expect(icon.target_id).to_equal("right_icon_1")
expect(bg.kind).to_equal("desktop_background")
expect(bg.handled).to_equal(true)
```

</details>

#### applies launch focus and drag commands to shared shell state

1. wm runtime shell state empty

2. shared wm dispatch pointer

3. shared wm dispatch pointer

4. shared wm dispatch pointer
   - Expected: launched.launched_apps.len() equals `1`
   - Expected: launched.launched_apps[0] equals `browser`
   - Expected: focused.focused_window_id equals `win1`
   - Expected: dragging.focused_window_id equals `win2`
   - Expected: dragging.dragging_surface_id equals `surf2`
   - Expected: dragging.last_command_kind equals `window_drag_begin`


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val launched = wm_runtime_apply_shared_dispatch(
    wm_runtime_shell_state_empty(),
    shared_wm_dispatch_pointer(_scene(), _taskbar(), 70, 575, "left", "down", 1000, "09:41", 2)
)
val focused = wm_runtime_apply_shared_dispatch(
    launched,
    shared_wm_dispatch_pointer(_scene(), _taskbar(), 120, 575, "left", "down", 1000, "09:41", 2)
)
val dragging = wm_runtime_apply_shared_dispatch(
    focused,
    shared_wm_dispatch_pointer(_scene(), _taskbar(), 90, 125, "left", "down", 1000, "09:41", 2)
)

expect(launched.launched_apps.len()).to_equal(1)
expect(launched.launched_apps[0]).to_equal("browser")
expect(focused.focused_window_id).to_equal("win1")
expect(dragging.focused_window_id).to_equal("win2")
expect(dragging.dragging_surface_id).to_equal("surf2")
expect(dragging.last_command_kind).to_equal("window_drag_begin")
```

</details>

#### applies command lane and background commands to shared shell state

1. wm runtime shell state empty

2. shared wm dispatch pointer

3. shared wm dispatch pointer

4. shared wm dispatch pointer
   - Expected: clock.command_lane_target equals `clock`
   - Expected: icon.command_lane_target equals `right_icon_1`
   - Expected: bg.focused_window_id equals ``
   - Expected: bg.dragging_surface_id equals ``
   - Expected: bg.background_click_count equals `1`
   - Expected: bg.last_command_kind equals `desktop_background`


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val clock = wm_runtime_apply_shared_dispatch(
    wm_runtime_shell_state_empty(),
    shared_wm_dispatch_pointer(_scene(), _taskbar(), 704, 8, "left", "down", 1000, "09:41", 2)
)
val icon = wm_runtime_apply_shared_dispatch(
    clock,
    shared_wm_dispatch_pointer(_scene(), _taskbar(), 780, 8, "left", "down", 1000, "09:41", 2)
)
val bg = wm_runtime_apply_shared_dispatch(
    icon,
    shared_wm_dispatch_pointer(_scene(), _taskbar(), 780, 300, "left", "down", 1000, "09:41", 2)
)

expect(clock.command_lane_target).to_equal("clock")
expect(icon.command_lane_target).to_equal("right_icon_1")
expect(bg.focused_window_id).to_equal("")
expect(bg.dragging_surface_id).to_equal("")
expect(bg.background_click_count).to_equal(1)
expect(bg.last_command_kind).to_equal("desktop_background")
```

</details>

#### keeps ignored commands fail-closed

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ignored = wm_runtime_dispatch_command("unknown", "", "", "", "", false)
val state = wm_runtime_apply_command(wm_runtime_shell_state_empty(), ignored)

expect(state.launched_apps.len()).to_equal(0)
expect(state.focused_window_id).to_equal("")
expect(state.last_command_kind).to_equal("ignored")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/wm_runtime_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- shared WM runtime dispatch adapter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
