# Wm Action Applier Specification

> 1. var compositor = Compositor with backends

<!-- sdn-diagram:id=wm_action_applier_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_action_applier_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_action_applier_spec -> std
wm_action_applier_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_action_applier_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Action Applier Specification

## Scenarios

### shared WM action applier

#### creates windows through shared compositor logic

1. var compositor = Compositor with backends
   - Expected: compositor.surfaces.len() equals `1`
   - Expected: compositor.surfaces[0].app_id equals `app.test`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var compositor = Compositor.with_backends(ApplierBackend(w: 200, h: 120), nil, 200, 120)
val result = apply_wm_action_to_compositor(compositor, _action("create_window", 0))
compositor = result.compositor
val wid = result.window_id
expect(wid > 0)
expect(compositor.surfaces.len()).to_equal(1)
expect(compositor.surfaces[0].app_id).to_equal("app.test")
```

</details>

#### creates web windows with a Simple Web render request surface

1. var compositor = Compositor with backends
   - Expected: compositor.surfaces.len() equals `1`
   - Expected: compositor.surfaces[0].title equals `Simple Browser`
   - Expected: compositor.surfaces[0].session.target equals `simple_web`
   - Expected: compositor.surfaces[0].session.surface_id equals `web_window_{result.window_id}`
   - Expected: compositor.surfaces[0].session.viewport_w equals `96`
   - Expected: compositor.surfaces[0].session.viewport_h equals `72`
   - Expected: req.target equals `simple_web`
   - Expected: req.surface_id equals `web_window_77`


<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var compositor = Compositor.with_backends(ApplierBackend(w: 200, h: 120), nil, 200, 120)
val action = WmAction(kind: "create_web_window", window_id: 0, title: "Simple Browser", x: 4, y: 6, width: 96, height: 72, content: "https://example.test", process_id: 700, app_id: "/host/browser", owner_port: 42, src_port: 0)
val result = apply_wm_action_to_compositor(compositor, action)
compositor = result.compositor
expect(result.applied)
expect(compositor.surfaces.len()).to_equal(1)
expect(compositor.surfaces[0].title).to_equal("Simple Browser")
expect(compositor.surfaces[0].session.target).to_equal("simple_web")
expect(compositor.surfaces[0].session.surface_id).to_equal("web_window_{result.window_id}")
expect(compositor.surfaces[0].session.viewport_w).to_equal(96)
expect(compositor.surfaces[0].session.viewport_h).to_equal(72)
expect(compositor.surfaces[0].session.wants_pixels)
expect(compositor.surfaces[0].session.body_html).to_contain("https://example.test")

val req = wm_action_web_window_request(77, "Browser", "about:blank", 64, 48)
expect(req.target).to_equal("simple_web")
expect(req.surface_id).to_equal("web_window_77")
expect(req.wants_pixels)
```

</details>

#### applies lifecycle changes through one helper

1. var compositor = Compositor with backends

2. compositor = apply wm action to compositor

3. compositor = apply wm action to compositor
   - Expected: compositor.surfaces[0].x equals `10`
   - Expected: compositor.surfaces[0].width equals `80`

4. compositor = apply wm action to compositor

5. compositor = apply wm action to compositor


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var compositor = Compositor.with_backends(ApplierBackend(w: 200, h: 120), nil, 200, 120)
val created = apply_wm_action_to_compositor(compositor, _action("create_window", 0))
compositor = created.compositor
val wid = created.window_id
compositor = apply_wm_action_to_compositor(compositor, _action("move", wid)).compositor
compositor = apply_wm_action_to_compositor(compositor, _action("resize", wid)).compositor
expect(compositor.surfaces[0].x).to_equal(10)
expect(compositor.surfaces[0].width).to_equal(80)
compositor = apply_wm_action_to_compositor(compositor, _action("minimize", wid)).compositor
expect(not compositor.surfaces[0].visible)
compositor = apply_wm_action_to_compositor(compositor, _action("restore", wid)).compositor
expect(compositor.surfaces[0].visible)
```

</details>

#### classifies shared lifecycle actions

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wm_action_is_shared_lifecycle("resize"))
val none_is_lifecycle = wm_action_is_shared_lifecycle("none")
expect(not none_is_lifecycle)
```

</details>

#### normalizes action app identity without changing lifecycle fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val action = _action("create_window", 0)
val normalized = wm_action_with_app_id(action, "launcher.app")
expect(normalized.kind).to_equal("create_window")
expect(normalized.title).to_equal(action.title)
expect(normalized.width).to_equal(action.width)
expect(normalized.owner_port).to_equal(action.owner_port)
expect(normalized.src_port).to_equal(action.src_port)
expect(normalized.app_id).to_equal("launcher.app")
```

</details>

#### builds remote update trees through shared compositor logic

1. var compositor = Compositor with backends
   - Expected: compositor.surfaces[0].session.root_id equals `remote_{created.window_id}`
   - Expected: tree.root_id equals `remote_44`
   - Expected: tree.title() equals `Window 44`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var compositor = Compositor.with_backends(ApplierBackend(w: 200, h: 120), nil, 200, 120)
val created = apply_wm_action_to_compositor(compositor, _action("create_window", 0))
compositor = created.compositor
val updated = apply_wm_action_to_compositor(compositor, _action("update_tree", created.window_id))
compositor = updated.compositor
expect(updated.applied)
expect(compositor.surfaces[0].session.root_id).to_equal("remote_{created.window_id}")

val tree = wm_action_remote_tree(44, "payload")
expect(tree.root_id).to_equal("remote_44")
expect(tree.title()).to_equal("Window 44")
```

</details>

#### builds shared lifecycle actions from host bridge requests

<details>
<summary>Executable SPipe</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val create = wm_action_from_bridge_request(42, COMP_CREATE_WINDOW.to_i64(), 0, "Host App", 12, 18, 240, 160, "initial", 700, "/host/app")
expect(create.kind).to_equal("create_window")
expect(create.owner_port).to_equal(42)
expect(create.process_id).to_equal(700)
expect(create.app_id).to_equal("/host/app")
val create_web = wm_action_from_bridge_request(42, COMP_CREATE_WEB_WINDOW.to_i64(), 0, "https://example.test", 12, 18, 240, 160, "https://example.test", 700, "/host/browser")
expect(create_web.kind).to_equal("create_web_window")
expect(create_web.content).to_equal("https://example.test")

val move_action = wm_action_from_bridge_request(42, COMP_MOVE.to_i64(), 9, "", 30, 40, 0, 0, "", 0, "")
val resize = wm_action_from_bridge_request(42, COMP_RESIZE.to_i64(), 9, "", 0, 0, 320, 220, "", 0, "")
val title = wm_action_from_bridge_request(42, COMP_SET_TITLE.to_i64(), 9, "Renamed", 0, 0, 0, 0, "", 0, "")
val update = wm_action_from_bridge_request(42, COMP_UPDATE_TREE.to_i64(), 9, "", 0, 0, 0, 0, "tree", 0, "")
val minimized = wm_action_from_bridge_request(42, COMP_MINIMIZE.to_i64(), 9, "", 0, 0, 0, 0, "", 0, "")
val restored = wm_action_from_bridge_request(42, COMP_RESTORE.to_i64(), 9, "", 0, 0, 0, 0, "", 0, "")

expect(move_action.kind).to_equal("move")
expect(move_action.x).to_equal(30)
expect(resize.kind).to_equal("resize")
expect(resize.width).to_equal(320)
expect(title.kind).to_equal("set_title")
expect(title.title).to_equal("Renamed")
expect(update.kind).to_equal("update_tree")
expect(update.content).to_equal("tree")
expect(minimized.kind).to_equal("minimize")
expect(restored.kind).to_equal("restore")
```

</details>

#### applies lifecycle actions to host-neutral window state

1. var result = apply wm action to lifecycle windows
   - Expected: result.window_id equals `1`
   - Expected: result.next_window_id equals `2`
   - Expected: windows.len() equals `1`

2. result = apply wm action to lifecycle windows
   - Expected: windows[0].x equals `40`
   - Expected: windows[0].y equals `50`

3. result = apply wm action to lifecycle windows
   - Expected: windows[0].w equals `320`
   - Expected: windows[0].h equals `220`

4. result = apply wm action to lifecycle windows

5. result = apply wm action to lifecycle windows
   - Expected: windows[0].x equals `0`
   - Expected: windows[0].y equals `48`
   - Expected: windows[0].w equals `640`
   - Expected: windows[0].h equals `384`

6. result = apply wm action to lifecycle windows
   - Expected: result.windows.len() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var windows: [WmLifecycleWindowState] = []
var result = apply_wm_action_to_lifecycle_windows(windows, 1, 640, 480, _action("create_window", 0))
windows = result.windows
expect(result.applied)
expect(result.window_id).to_equal(1)
expect(result.next_window_id).to_equal(2)
expect(windows.len()).to_equal(1)
expect(windows[0].focused)

result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, wm_move_action(1, 40, 50))
windows = result.windows
expect(windows[0].x).to_equal(40)
expect(windows[0].y).to_equal(50)

result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, wm_resize_action(1, 320, 220))
windows = result.windows
expect(windows[0].w).to_equal(320)
expect(windows[0].h).to_equal(220)

result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, wm_focus_action(1))
windows = result.windows
expect(windows[0].focused)

result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, _action("maximize", 1))
windows = result.windows
expect(windows[0].x).to_equal(0)
expect(windows[0].y).to_equal(48)
expect(windows[0].w).to_equal(640)
expect(windows[0].h).to_equal(384)

result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, wm_destroy_action(1))
expect(result.windows.len()).to_equal(0)
```

</details>

#### keeps one focused top window across minimize restore maximize and destroy

1. var result = apply wm action to lifecycle windows

2. result = apply wm action to lifecycle windows
   - Expected: windows[0].id equals `1`
   - Expected: windows[1].id equals `2`

3. result = apply wm action to lifecycle windows
   - Expected: windows[0].id equals `2`
   - Expected: windows[1].id equals `1`

4. result = apply wm action to lifecycle windows
   - Expected: windows[0].id equals `1`
   - Expected: windows[1].id equals `2`

5. result = apply wm action to lifecycle windows
   - Expected: windows[0].id equals `2`
   - Expected: windows[1].id equals `1`
   - Expected: windows[1].x equals `0`
   - Expected: windows[1].y equals `48`

6. result = apply wm action to lifecycle windows
   - Expected: windows.len() equals `1`
   - Expected: windows[0].id equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var windows: [WmLifecycleWindowState] = []
var result = apply_wm_action_to_lifecycle_windows(windows, 1, 640, 480, _action("create_window", 0))
windows = result.windows
result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, _action("create_window", 0))
windows = result.windows
expect(windows[0].id).to_equal(1)
expect(not windows[0].focused)
expect(windows[1].id).to_equal(2)
expect(windows[1].focused)

result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, _action("minimize", 2))
windows = result.windows
expect(windows[0].id).to_equal(2)
expect(windows[0].minimized)
expect(not windows[0].focused)
expect(windows[1].id).to_equal(1)
expect(windows[1].focused)

result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, _action("restore", 2))
windows = result.windows
expect(windows[0].id).to_equal(1)
expect(not windows[0].focused)
expect(windows[1].id).to_equal(2)
expect(not windows[1].minimized)
expect(windows[1].focused)

result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, _action("maximize", 1))
windows = result.windows
expect(windows[0].id).to_equal(2)
expect(not windows[0].focused)
expect(windows[1].id).to_equal(1)
expect(windows[1].focused)
expect(windows[1].x).to_equal(0)
expect(windows[1].y).to_equal(48)

result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, wm_destroy_action(1))
windows = result.windows
expect(windows.len()).to_equal(1)
expect(windows[0].id).to_equal(2)
expect(windows[0].focused)
```

</details>

#### derives modern motion phases from lifecycle actions and window state

<details>
<summary>Executable SPipe</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val window = WmLifecycleWindowState(id: 3, owner_port: 11, title: "Motion", x: 20, y: 60, w: 200, h: 140, content: "", process_id: 1, app_id: "/motion", minimized: false, focused: true)
val minimized = WmLifecycleWindowState(id: 4, owner_port: 11, title: "Minimized", x: 20, y: 60, w: 200, h: 140, content: "", process_id: 1, app_id: "/motion", minimized: true, focused: false)
expect(wm_lifecycle_motion_phase("create_window", window)).to_equal("opening")
expect(wm_lifecycle_motion_phase("create_web_window", window)).to_equal("opening")
expect(wm_lifecycle_motion_phase("destroy_window", window)).to_equal("closing")
expect(wm_lifecycle_motion_phase("minimize", window)).to_equal("minimizing")
expect(wm_lifecycle_motion_phase("restore", minimized)).to_equal("restoring")
expect(wm_lifecycle_motion_phase("maximize", minimized)).to_equal("restoring")
expect(wm_lifecycle_motion_phase("focus", window)).to_equal("focused")
expect(wm_lifecycle_motion_phase("move", minimized)).to_equal("minimized")
val contract = wm_lifecycle_motion_contract("restore", minimized)
val opening = wm_lifecycle_motion_contract("create_window", window)
val closing = wm_lifecycle_motion_contract("destroy_window", window)
val focused = wm_lifecycle_motion_contract("focus", window)
val idle = wm_lifecycle_motion_contract("move", window)
val minimized_idle = wm_lifecycle_motion_contract("move", minimized)
expect(contract.class_name).to_equal("wm-window-restoring")
expect(contract.duration_ms).to_equal(240)
expect(contract.reduced_duration_ms).to_equal(80)
expect(contract.can_disable)
expect(contract.easing).to_equal("cubic-bezier(.2,.8,.2,1)")
expect(contract.transform_origin).to_equal("dock")
expect(contract.dock_origin_x).to_equal(120)
expect(contract.dock_origin_y).to_equal(248)
expect(opening.easing).to_equal("cubic-bezier(.2,.8,.2,1)")
expect(opening.transform_origin).to_equal("center")
expect(closing.easing).to_equal("cubic-bezier(.4,0,.2,1)")
expect(closing.transform_origin).to_equal("center")
expect(focused.easing).to_equal("ease")
expect(focused.reduced_duration_ms).to_equal(80)
expect(idle.easing).to_equal("ease")
expect(idle.reduced_duration_ms).to_equal(0)
expect(minimized_idle.class_name).to_equal("wm-window-minimized")
expect(minimized_idle.duration_ms).to_equal(0)
expect(minimized_idle.reduced_duration_ms).to_equal(0)
val summary = wm_lifecycle_motion_summary("minimize", window)
expect(summary).to_contain("phase=minimizing")
expect(summary).to_contain("class=wm-window-minimizing")
expect(summary).to_contain("easing=cubic-bezier(.4,0,.2,1)")
expect(summary).to_contain("origin=dock")
expect(summary).to_contain("dock_origin=120,248")
expect(summary).to_contain("can_disable=true")
```

</details>

#### handles taskbar hit testing in host-neutral lifecycle state

1. WmLifecycleWindowState

2. WmLifecycleWindowState
   - Expected: wm_lifecycle_hit_taskbar(windows, 640, 480, first_x + (item_w / 2), dock_y + 16) equals `1`
   - Expected: wm_lifecycle_hit_taskbar(windows, 640, 480, first_x + (item_w / 2), dock_y - 1) equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val windows = [
    WmLifecycleWindowState(id: 1, owner_port: 11, title: "One", x: 20, y: 60, w: 200, h: 140, content: "", process_id: 1, app_id: "/one", minimized: false, focused: false),
    WmLifecycleWindowState(id: 2, owner_port: 22, title: "Two", x: 40, y: 80, w: 200, h: 140, content: "", process_id: 2, app_id: "/two", minimized: false, focused: true)
]
val item_w = wm_taskbar_item_width(640, windows.len())
val first_x = wm_taskbar_item_x(640, windows.len(), 0)
val dock_y = 480 - 62
expect(wm_taskbar_dock_width(640, windows.len())).to_be_less_than(640)
expect(wm_lifecycle_hit_taskbar(windows, 640, 480, first_x + (item_w / 2), dock_y + 16)).to_equal(1)
expect(wm_lifecycle_hit_taskbar(windows, 640, 480, first_x + (item_w / 2), dock_y - 1)).to_equal(0)
```

</details>

#### moves and resizes lifecycle windows from host-neutral pointer state

1. WmLifecycleWindowState
   - Expected: moved.windows[0].x equals `0`
   - Expected: moved.windows[0].y equals `48`
   - Expected: grip.interaction.resize_window_id equals `7`
   - Expected: resized.windows[0].w equals `160`
   - Expected: resized.windows[0].h equals `120`
   - Expected: up.resize_window_id equals `0`
   - Expected: drag_up.drag_window_id equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val windows = [
    WmLifecycleWindowState(id: 7, owner_port: 11, title: "Drag", x: 40, y: 70, w: 200, h: 160, content: "", process_id: 1, app_id: "/drag", minimized: false, focused: true)
]
val drag = WmPointerInteractionState(dragging: true, drag_window_id: 7, drag_offset_x: 60, drag_offset_y: 40, resizing: false, resize_window_id: 0, resize_start_x: 0, resize_start_y: 0, resize_start_w: 0, resize_start_h: 0)
val moved = wm_lifecycle_pointer_move(windows, 8, 640, 480, drag, -20, 10)
expect(moved.windows[0].x).to_equal(0)
expect(moved.windows[0].y).to_equal(48)

val probe = WmPointerInteractionState(dragging: false, drag_window_id: 0, drag_offset_x: 0, drag_offset_y: 0, resizing: false, resize_window_id: 0, resize_start_x: 0, resize_start_y: 0, resize_start_w: 0, resize_start_h: 0)
val grip = wm_lifecycle_pointer_move(windows, 8, 640, 480, probe, 238, 228)
expect(grip.interaction.resize_window_id).to_equal(7)
val down = wm_lifecycle_left_button(grip.interaction, true)
expect(down.resizing)
val resized = wm_lifecycle_pointer_move(windows, 8, 640, 480, down, 0, 0)
expect(resized.windows[0].w).to_equal(160)
expect(resized.windows[0].h).to_equal(120)
val up = wm_lifecycle_left_button(resized.interaction, false)
expect(not up.resizing)
expect(up.resize_window_id).to_equal(0)
val dragging = WmPointerInteractionState(dragging: true, drag_window_id: 7, drag_offset_x: 60, drag_offset_y: 40, resizing: false, resize_window_id: 0, resize_start_x: 0, resize_start_y: 0, resize_start_w: 0, resize_start_h: 0)
val drag_up = wm_lifecycle_left_button(dragging, false)
expect(not drag_up.dragging)
expect(drag_up.drag_window_id).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/wm_action_applier_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- shared WM action applier

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
