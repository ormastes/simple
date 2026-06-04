# Window Scene Specification

> 1. var manager = WindowManager for backend

<!-- sdn-diagram:id=window_scene_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=window_scene_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

window_scene_spec -> std
window_scene_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=window_scene_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window Scene Specification

## Scenarios

### SharedWmScene

#### projects WindowManager state and registry identity into a common scene

1. var manager = WindowManager for backend

2. var registry = UiWindowSurfaceRegistry new

3. registry bind with kind
   - Expected: scene.width equals `800`
   - Expected: scene.height equals `600`
   - Expected: scene.backend equals `tauri`
   - Expected: scene.windows.len() equals `1`
   - Expected: scene.windows[0].surface_id equals `surf1`
   - Expected: scene.windows[0].window_id equals `win1`
   - Expected: scene.windows[0].surface_kind equals `UI_SURFACE_KIND_SIMPLE_WEB`
   - Expected: shared_wm_focused_window_id(scene) equals `win1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = WindowManager.for_backend("tauri")
val _ = manager.open_window("surf1", "Window One", 10, 20, 300, 200, _tree("one"))
var registry = UiWindowSurfaceRegistry.new()
registry.bind_with_kind("win1", "surf1", 42u64, "demo.app", "Window One", UI_SURFACE_KIND_SIMPLE_WEB)

val scene = shared_wm_scene_from_window_manager(manager, registry, 800, 600)

expect(scene.width).to_equal(800)
expect(scene.height).to_equal(600)
expect(scene.backend).to_equal("tauri")
expect(scene.windows.len()).to_equal(1)
expect(scene.windows[0].surface_id).to_equal("surf1")
expect(scene.windows[0].window_id).to_equal("win1")
expect(scene.windows[0].surface_kind).to_equal(UI_SURFACE_KIND_SIMPLE_WEB)
expect(shared_wm_focused_window_id(scene)).to_equal("win1")
```

</details>

#### omits minimized windows from the visible projection

1. var manager = WindowManager new

2. manager minimize window
   - Expected: scene.windows.len() equals `2`
   - Expected: visible.len() equals `1`
   - Expected: visible[0].surface_id equals `surf1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = WindowManager.new()
val _a = manager.open_window("surf1", "One", 10, 20, 300, 200, _tree("one"))
val _b = manager.open_window("surf2", "Two", 30, 40, 300, 200, _tree("two"))
manager.minimize_window("surf2")
val registry = UiWindowSurfaceRegistry.new()

val scene = shared_wm_scene_from_window_manager(manager, registry, 800, 600)
val visible = shared_wm_visible_windows(scene)

expect(scene.windows.len()).to_equal(2)
expect(visible.len()).to_equal(1)
expect(visible[0].surface_id).to_equal("surf1")
```

</details>

#### projects top command lane, bottom taskbar, background, and DPI scaled content bounds

1. var manager = WindowManager new
   - Expected: chrome.background_color equals `#101418`
   - Expected: chrome.command_lane.x equals `0`
   - Expected: chrome.command_lane.y equals `0`
   - Expected: chrome.command_lane.width equals `800`
   - Expected: chrome.command_lane.height equals `32`
   - Expected: chrome.content_area.y equals `32`
   - Expected: chrome.content_area.height equals `520`
   - Expected: chrome.taskbar.y equals `552`
   - Expected: chrome.taskbar.height equals `48`
   - Expected: chrome.clock_label equals `09:41`
   - Expected: chrome.right_icon_count equals `3`
   - Expected: chrome.taskbar_icon_count equals `5`
   - Expected: hi_dpi.command_lane.height equals `64`
   - Expected: hi_dpi.taskbar.height equals `96`
   - Expected: hi_dpi.content_area.height equals `440`


<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = WindowManager.new()
val _ = manager.open_window("surf1", "One", 10, 40, 300, 200, _tree("one"))
val scene = shared_wm_scene_from_window_manager(manager, UiWindowSurfaceRegistry.new(), 800, 600)

val chrome = shared_wm_scene_chrome(scene, 1000, "09:41", 3, 5)
expect(chrome.background_color).to_equal("#101418")
expect(chrome.command_lane.x).to_equal(0)
expect(chrome.command_lane.y).to_equal(0)
expect(chrome.command_lane.width).to_equal(800)
expect(chrome.command_lane.height).to_equal(32)
expect(chrome.content_area.y).to_equal(32)
expect(chrome.content_area.height).to_equal(520)
expect(chrome.taskbar.y).to_equal(552)
expect(chrome.taskbar.height).to_equal(48)
expect(chrome.clock_label).to_equal("09:41")
expect(chrome.right_icon_count).to_equal(3)
expect(chrome.taskbar_icon_count).to_equal(5)

val hi_dpi = shared_wm_scene_chrome(scene, 2000, "09:41", 1, 2)
expect(hi_dpi.command_lane.height).to_equal(64)
expect(hi_dpi.taskbar.height).to_equal(96)
expect(hi_dpi.content_area.height).to_equal(440)
```

</details>

#### clamps inner window drag to the desktop content area

1. var manager = WindowManager new
   - Expected: dragged_min.windows[0].x equals `0`
   - Expected: dragged_min.windows[0].y equals `32`
   - Expected: dragged_min.windows[0].focused is true
   - Expected: dragged_max.windows[0].x equals `500`
   - Expected: dragged_max.windows[0].y equals `352`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = WindowManager.new()
val _ = manager.open_window("surf1", "One", 10, 40, 300, 200, _tree("one"))
val scene = shared_wm_scene_from_window_manager(manager, UiWindowSurfaceRegistry.new(), 800, 600)

val dragged_min = shared_wm_drag_window(scene, "surf1", -100, -100)
expect(dragged_min.windows[0].x).to_equal(0)
expect(dragged_min.windows[0].y).to_equal(32)
expect(dragged_min.windows[0].focused).to_equal(true)

val dragged_max = shared_wm_drag_window(scene, "surf1", 1000, 1000)
expect(dragged_max.windows[0].x).to_equal(500)
expect(dragged_max.windows[0].y).to_equal(352)
```

</details>

#### dispatches command lane clock and right icon clicks

1. var manager = WindowManager new
   - Expected: clock.action equals `command_lane_clock`
   - Expected: clock.target_id equals `clock`
   - Expected: icon.action equals `command_lane_icon`
   - Expected: icon.target_id equals `right_icon_1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = WindowManager.new()
val _ = manager.open_window("surf1", "One", 10, 40, 300, 200, _tree("one"))
val scene = shared_wm_scene_from_window_manager(manager, UiWindowSurfaceRegistry.new(), 800, 600)

val clock = shared_wm_dispatch_pointer(scene, _taskbar(), 704, 8, "left", "down", 1000, "09:41", 2)
val icon = shared_wm_dispatch_pointer(scene, _taskbar(), 780, 8, "left", "down", 1000, "09:41", 2)

expect(clock.action).to_equal("command_lane_clock")
expect(clock.target_id).to_equal("clock")
expect(icon.action).to_equal("command_lane_icon")
expect(icon.target_id).to_equal("right_icon_1")
```

</details>

#### dispatches bottom taskbar pinned app launch and running window focus

1. var manager = WindowManager new

2. var registry = UiWindowSurfaceRegistry new

3. registry bind with kind

4. registry bind with kind
   - Expected: launch.action equals `launch_app`
   - Expected: launch.app_id equals `browser`
   - Expected: focus.action equals `focus_window`
   - Expected: focus.window_id equals `win1`
   - Expected: shared_wm_focused_window_id(focus.scene) equals `win1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = WindowManager.new()
val _one = manager.open_window("surf1", "One", 10, 40, 300, 200, _tree("one"))
val _two = manager.open_window("surf2", "Two", 80, 120, 300, 200, _tree("two"))
var registry = UiWindowSurfaceRegistry.new()
registry.bind_with_kind("win1", "surf1", 42u64, "demo.app", "Window One", UI_SURFACE_KIND_SIMPLE_WEB)
registry.bind_with_kind("win2", "surf2", 43u64, "demo.two", "Window Two", UI_SURFACE_KIND_SIMPLE_WEB)
val scene = shared_wm_scene_from_window_manager(manager, registry, 800, 600)
val taskbar = _taskbar()

val launch = shared_wm_dispatch_pointer(scene, taskbar, 70, 575, "left", "down", 1000, "09:41", 2)
val focus = shared_wm_dispatch_pointer(scene, taskbar, 120, 575, "left", "down", 1000, "09:41", 2)

expect(launch.action).to_equal("launch_app")
expect(launch.app_id).to_equal("browser")
expect(focus.action).to_equal("focus_window")
expect(focus.window_id).to_equal("win1")
expect(shared_wm_focused_window_id(focus.scene)).to_equal("win1")
```

</details>

#### dispatches titlebar clicks as window drag starts and body clicks as focus

1. var manager = WindowManager new

2. var registry = UiWindowSurfaceRegistry new

3. registry bind with kind

4. registry bind with kind
   - Expected: drag.action equals `begin_drag_window`
   - Expected: drag.target_id equals `surf2`
   - Expected: shared_wm_focused_window_id(drag.scene) equals `win2`
   - Expected: focus.action equals `focus_window`
   - Expected: focus.window_id equals `win2`
   - Expected: background.action equals `desktop_background`


<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = WindowManager.new()
val _one = manager.open_window("surf1", "One", 10, 40, 300, 200, _tree("one"))
val _two = manager.open_window("surf2", "Two", 80, 120, 300, 200, _tree("two"))
var registry = UiWindowSurfaceRegistry.new()
registry.bind_with_kind("win1", "surf1", 42u64, "demo.app", "Window One", UI_SURFACE_KIND_SIMPLE_WEB)
registry.bind_with_kind("win2", "surf2", 43u64, "demo.two", "Window Two", UI_SURFACE_KIND_SIMPLE_WEB)
val scene = shared_wm_scene_from_window_manager(manager, registry, 800, 600)

val drag = shared_wm_dispatch_pointer(scene, _taskbar(), 90, 125, "left", "down", 1000, "09:41", 2)
val focus = shared_wm_dispatch_pointer(scene, _taskbar(), 90, 180, "left", "down", 1000, "09:41", 2)
val background = shared_wm_dispatch_pointer(scene, _taskbar(), 780, 300, "left", "down", 1000, "09:41", 2)

expect(drag.action).to_equal("begin_drag_window")
expect(drag.target_id).to_equal("surf2")
expect(shared_wm_focused_window_id(drag.scene)).to_equal("win2")
expect(focus.action).to_equal("focus_window")
expect(focus.window_id).to_equal("win2")
expect(background.action).to_equal("desktop_background")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/window_scene_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SharedWmScene

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
