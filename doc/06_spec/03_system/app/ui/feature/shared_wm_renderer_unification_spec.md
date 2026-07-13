# Shared Wm Renderer Unification Specification

> 1. var result = apply wm action to lifecycle windows

<!-- sdn-diagram:id=shared_wm_renderer_unification_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shared_wm_renderer_unification_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shared_wm_renderer_unification_spec -> std
shared_wm_renderer_unification_spec -> common
shared_wm_renderer_unification_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shared_wm_renderer_unification_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared Wm Renderer Unification Specification

## Scenarios

### shared WM renderer unification behavior contract

#### uses one host-neutral lifecycle path for create move resize maximize and destroy

1. var result = apply wm action to lifecycle windows
   - Expected: _applied_flag(result.applied) equals `1`
   - Expected: windows.len() equals `1`
   - Expected: _applied_flag(windows[0].focused) equals `1`

2. result = apply wm action to lifecycle windows

3. result = apply wm action to lifecycle windows
   - Expected: windows[0].x equals `48`
   - Expected: windows[0].y equals `52`
   - Expected: windows[0].w equals `144`
   - Expected: windows[0].h equals `104`

4. result = apply wm action to lifecycle windows
   - Expected: windows[0].x equals `0`
   - Expected: windows[0].y equals `48`
   - Expected: windows[0].w equals `640`
   - Expected: windows[0].h equals `384`

5. result = apply wm action to lifecycle windows
   - Expected: result.windows.len() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var windows: [WmLifecycleWindowState] = []
var result = apply_wm_action_to_lifecycle_windows(windows, 1, 640, 480, _action("create_window", 0))
windows = result.windows
expect(_applied_flag(result.applied)).to_equal(1)
expect(windows.len()).to_equal(1)
expect(_applied_flag(windows[0].focused)).to_equal(1)

result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, wm_move_action(1, 48, 52))
windows = result.windows
result = apply_wm_action_to_lifecycle_windows(windows, result.next_window_id, 640, 480, wm_resize_action(1, 144, 104))
windows = result.windows
expect(windows[0].x).to_equal(48)
expect(windows[0].y).to_equal(52)
expect(windows[0].w).to_equal(144)
expect(windows[0].h).to_equal(104)

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

#### routes the same lifecycle bridge sequence through the SimpleOS GUI adapter

1. adapter deliver bridge request

2. adapter deliver bridge request

3. adapter deliver bridge request

4. adapter deliver bridge request

5. adapter deliver bridge request

6. adapter deliver bridge request

7. adapter deliver bridge request

8. adapter deliver bridge request
   - Expected: adapter.compositor.windows[0].x equals `0`
   - Expected: adapter.compositor.windows[0].y equals `48`
   - Expected: adapter.compositor.windows[0].w equals `320`
   - Expected: adapter.compositor.windows[0].h equals `144`
   - Expected: _applied_flag(adapter.compositor.windows[0].minimized) equals `0`
   - Expected: _applied_flag(adapter.compositor.windows[0].focused) equals `1`
   - Expected: adapter.compositor.windows[0].title equals `Terminal Renamed`
   - Expected: adapter.compositor.windows[0].content equals `updated`

9. adapter deliver bridge request
   - Expected: adapter.compositor.windows.len() equals `0`
   - Expected: adapter.delivered_bridge_events equals `9`


<details>
<summary>Executable SPipe</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = SimpleOsGuiAdapter.new(_backend(320, 240), Size.wh(320, 240))

adapter.deliver_bridge_request(1, 44, COMP_CREATE_WINDOW.to_i64(), 0, "Terminal", 24, 36, 128, 92, "ready", 800, "/sys/apps/terminal")
val wid = adapter.compositor.windows[0].id
adapter.deliver_bridge_request(2, 44, COMP_MOVE.to_i64(), wid, "", 48, 52, 0, 0, "", 0, "/sys/apps/terminal")
adapter.deliver_bridge_request(3, 44, COMP_RESIZE.to_i64(), wid, "", 0, 0, 144, 104, "", 0, "/sys/apps/terminal")
adapter.deliver_bridge_request(4, 44, COMP_MINIMIZE.to_i64(), wid, "", 0, 0, 0, 0, "", 0, "/sys/apps/terminal")
adapter.deliver_bridge_request(5, 44, COMP_RESTORE.to_i64(), wid, "", 0, 0, 0, 0, "", 0, "/sys/apps/terminal")
adapter.deliver_bridge_request(6, 44, COMP_SET_TITLE.to_i64(), wid, "Terminal Renamed", 0, 0, 0, 0, "", 0, "/sys/apps/terminal")
adapter.deliver_bridge_request(7, 44, COMP_MAXIMIZE.to_i64(), wid, "", 0, 0, 0, 0, "", 0, "/sys/apps/terminal")
adapter.deliver_bridge_request(8, 44, COMP_UPDATE_TREE.to_i64(), wid, "", 0, 0, 0, 0, "updated", 0, "/sys/apps/terminal")

expect(adapter.compositor.windows[0].x).to_equal(0)
expect(adapter.compositor.windows[0].y).to_equal(48)
expect(adapter.compositor.windows[0].w).to_equal(320)
expect(adapter.compositor.windows[0].h).to_equal(144)
expect(_applied_flag(adapter.compositor.windows[0].minimized)).to_equal(0)
expect(_applied_flag(adapter.compositor.windows[0].focused)).to_equal(1)
expect(adapter.compositor.windows[0].title).to_equal("Terminal Renamed")
expect(adapter.compositor.windows[0].content).to_equal("updated")

adapter.deliver_bridge_request(9, 44, COMP_DESTROY_WINDOW.to_i64(), wid, "", 0, 0, 0, 0, "", 0, "/sys/apps/terminal")
expect(adapter.compositor.windows.len()).to_equal(0)
expect(adapter.delivered_bridge_events).to_equal(9)
```

</details>

#### materializes host web windows as Simple Web render request surfaces

1. var compositor = Compositor with backends
   - Expected: _applied_flag(result.applied) equals `1`
   - Expected: compositor.surfaces.len() equals `1`
   - Expected: compositor.surfaces[0].session.target equals `simple_web`
   - Expected: compositor.surfaces[0].session.viewport_w equals `96`
   - Expected: compositor.surfaces[0].session.viewport_h equals `72`
   - Expected: _applied_flag(compositor.surfaces[0].session.wants_pixels) equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var compositor = Compositor.with_backends(_backend(200, 120), nil, 200, 120)
val action = wm_action_from_bridge_request(42, COMP_CREATE_WEB_WINDOW.to_i64(), 0, "https://example.test", 12, 18, 96, 72, "https://example.test", 700, "/host/browser")
val result = apply_wm_action_to_compositor(compositor, action)
compositor = result.compositor

expect(_applied_flag(result.applied)).to_equal(1)
expect(compositor.surfaces.len()).to_equal(1)
expect(compositor.surfaces[0].session.target).to_equal("simple_web")
expect(compositor.surfaces[0].session.viewport_w).to_equal(96)
expect(compositor.surfaces[0].session.viewport_h).to_equal(72)
expect(_applied_flag(compositor.surfaces[0].session.wants_pixels)).to_equal(1)
expect(compositor.surfaces[0].session.body_html).to_contain("https://example.test")
```

</details>

#### renders the live rich scene behind the shared CompositorBackend surface

1. var backend =  backend

2. Render the revision-matched Simple Web frame through the shared WM scene renderer
   - Expected: fill_seen equals `1`
   - Expected: text_seen equals `1`
   - Expected: backend.present_count equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = _backend(800, 600)
val window = simple_gui_internal_window(
    "surface-41", "41", 7001u64, "editor", "Live Editor",
    80, 70, 420, 300, "document=notes.spl", false, true, 0
)
val scene = simple_gui_internal_window_scene(800, 600, "simpleos-compositor", [window])
val pixels = _solid_pixels(412 * 264, 0xFF102030u32)
val frame = WmContentFrame(window_id: "41", scene_revision: 7, content_revision: 3, origin_kind: WM_CONTENT_ORIGIN_SIMPLE_WEB, width: 412, height: 264, pixels: pixels, checksum: wm_content_frame_checksum(pixels), parent_window_id: "", offset_x: 0, offset_y: 0)
render_baremetal_shared_wm_scene(backend, scene, empty_taskbar_model(), [frame], 7, 9, "12:34")

val fill_seen = if backend.fill_count > 0: 1 else: 0
val text_seen = if backend.text_count > 0: 1 else: 0
expect(fill_seen).to_equal(1)
expect(text_seen).to_equal(1)
expect(backend.blit_count).to_equal(1)
expect(backend.present_count).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/ui/feature/shared_wm_renderer_unification_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- shared WM renderer unification behavior contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
