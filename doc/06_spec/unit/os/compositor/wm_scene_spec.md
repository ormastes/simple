# Wm Scene Specification

## Scenarios

### WmScene — standard_wm_scene

#### scene structure

#### AC-2: standard scene has correct dimensions

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
expect(scene.width).to_equal(W)
expect(scene.height).to_equal(H)
```

</details>

#### AC-2: standard scene has a name

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val has_name = scene.name.len() > 0
expect(has_name)
```

</details>

#### AC-2: standard scene contains multiple elements

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
expect(scene.elements.len()).to_be_greater_than(0)
```

</details>

#### scene elements

#### AC-2: scene contains a desktop chrome element

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
var found = false
for elem in scene.elements:
    if elem.kind == "desktop_chrome":
        found = true
expect(found)
```

</details>

#### AC-2: scene contains a window decoration element

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
var found = false
for elem in scene.elements:
    if elem.kind == "decoration":
        found = true
expect(found)
```

</details>

#### AC-2: scene contains a glass panel element

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
var found = false
for elem in scene.elements:
    if elem.kind == "glass_panel":
        found = true
expect(found)
```

</details>

#### AC-2: scene contains a text label element

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
var found = false
for elem in scene.elements:
    if elem.kind == "text_label":
        found = true
expect(found)
```

</details>

#### AC-3: scene element positions are within bounds

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
var all_in_bounds = true
for elem in scene.elements:
    if elem.x < 0 or elem.y < 0:
        all_in_bounds = false
    if elem.x + elem.w > W or elem.y + elem.h > H:
        all_in_bounds = false
expect(all_in_bounds)
```

</details>

### WmScene — render_scene_to_backend

#### pixel buffer output

#### AC-3: rendered scene returns non-empty pixel buffer

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
# Note: requires BrowserCompositorBackend — will fail without impl
val pixels = render_scene_to_backend(scene, nil)
expect(pixels.len()).to_be_greater_than(0)
```

</details>

#### AC-3: render_scene_to_backend reuses a provided backend

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = WmSceneSpec(name: "empty_scene", width: W, height: H, elements: [])
val backend = BrowserCompositorBackend.with_color(W, H, 0xFF123456)
val pixels = render_scene_to_backend(scene, backend)
expect(pixels[0]).to_equal(0xFF123456)
```

</details>

#### AC-3: rendered pixel buffer has correct size (width * height)

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val pixels = render_scene_to_backend(scene, nil)
val expected_len = W * H
expect(pixels.len().to_i32()).to_equal(expected_len)
```

</details>

#### AC-3: rendered pixels are non-zero (not all transparent)

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val pixels = render_scene_to_backend(scene, nil)
var has_nonzero = false
for p in pixels:
    if p != 0:
        has_nonzero = true
expect(has_nonzero)
```

</details>

#### AC-3: small scenes render through the Simple Web Renderer pixel path

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(80, 60)
val pixels = render_scene_to_backend(scene, nil)
val html = scene_to_html(scene)
val req = WebRenderRequest.html(WEB_RENDER_TARGET_SIMPLE_WEB, scene.name, html, "", "", 80, 60).with_pixel_output()
val expected = compositor_render_html_pixels(req, html)
expect(pixels.len()).to_equal(80 * 60)
expect(pixels[0]).to_equal(expected[0])
expect(pixels[pixels.len() - 1]).to_equal(expected[expected.len() - 1])
```

</details>

### WmScene — scene_to_html

#### HTML output

#### AC-2: scene produces non-empty HTML

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val html = scene_to_html(scene)
expect(html.len()).to_be_greater_than(0)
```

</details>

#### AC-2: HTML contains doctype or html tag

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val html = scene_to_html(scene)
val has_html = html.contains("<html") or html.contains("<!DOCTYPE")
expect(has_html)
```

</details>

#### AC-2: HTML contains style information for glass panel

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val html = scene_to_html(scene)
val has_style = html.contains("backdrop-filter") or html.contains("blur")
expect(has_style)
```

</details>

#### AC-2: HTML dimensions match scene dimensions

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val html = scene_to_html(scene)
val has_width = html.contains("800")
expect(has_width)
```

</details>

#### AC-2: HTML exposes modern WM chrome controls and rounded translucent shell markers

<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val html = scene_to_html(scene)
expect(html).to_contain("data-modern-wm='true'")
expect(html).to_contain("data-theme-configured='true'")
expect(html).to_contain("data-window-radius-px='18'")
expect(html).to_contain("data-widget-radius-px='14'")
expect(html).to_contain("data-taskbar-radius-px='999'")
expect(html).to_contain("data-blur-px='24'")
expect(html).to_contain("data-desktop-layer-z='0'")
expect(html).to_contain("data-window-layer-z='20'")
expect(html).to_contain("data-overlay-layer-z='11000'")
expect(html).to_contain("data-standard-motion-ms='240'")
expect(html).to_contain("data-reduced-motion-ms='80'")
expect(html).to_contain("traffic-close")
expect(html).to_contain("traffic-min")
expect(html).to_contain("traffic-max")
expect(html).to_contain("bar-command")
expect(html).to_contain("bar-context")
expect(html).to_contain("border-radius:18px 18px 0 0")
expect(html).to_contain("border-radius:999px")
expect(html).to_contain("radial-gradient")
expect(html).to_contain("backdrop-filter:blur(24px)")
```

</details>

#### AC-2: exposes a deterministic modern theme configuration for OS renderers

<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = modern_wm_scene_theme_config()
expect(config.background_color).to_equal(0xFF0F172Au32)
expect(config.foreground_color).to_equal(0xFFFFFFFFu32)
expect(config.accent_color).to_equal(0xFF2563EBu32)
expect(config.titlebar_height_px).to_equal(32)
expect(config.command_lane_height_px).to_equal(32)
expect(config.taskbar_height_px).to_equal(56)
expect(config.window_radius_px).to_equal(18)
expect(config.widget_radius_px).to_equal(14)
expect(config.taskbar_radius_px).to_equal(999)
expect(config.control_radius_px).to_equal(12)
expect(config.icon_radius_px).to_equal(999)
expect(config.blur_px).to_equal(24)
expect(config.desktop_layer_z).to_equal(0)
expect(config.snap_layer_z).to_equal(15)
expect(config.window_layer_z).to_equal(20)
expect(config.overlay_layer_z).to_equal(11000)
expect(config.standard_motion_ms).to_equal(240)
expect(config.reduced_motion_ms).to_equal(80)
expect(config.can_disable_motion)
```

</details>

### WmScene — SharedWmScene projection

#### projects shared GUI windows into pure Simple WM scene elements

1. var manager = WindowManager new

2. manager minimize window

3. var registry = UiWindowSurfaceRegistry new

4. registry bind with kind
   - Expected: scene.width equals `640`
   - Expected: scene.height equals `480`
   - Expected: scene.elements.len() equals `4`

5. expect not


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = WindowManager.new()
val _one = manager.open_window("surf1", "Terminal", 20, 30, 300, 200, _shared_tree("terminal"))
val _two = manager.open_window("surf2", "Hidden", 40, 50, 300, 200, _shared_tree("hidden"))
manager.minimize_window("surf2")
var registry = UiWindowSurfaceRegistry.new()
registry.bind_with_kind("win1", "surf1", 77u64, "simple.terminal", "Terminal", UI_SURFACE_KIND_SIMPLE_WEB)

val shared = shared_wm_scene_from_window_manager(manager, registry, 640, 480)
val scene = shared_wm_scene_to_wm_scene(shared)
val html = scene_to_html(scene)

expect(scene.width).to_equal(640)
expect(scene.height).to_equal(480)
expect(scene.elements.len()).to_equal(4)
expect(html).to_contain("Terminal")
expect_not(html.contains("Hidden"))
```

</details>

#### projects shared command lane, clock, right icons, taskbar launchers, and windows into render elements

1. var manager = WindowManager new

2. var registry = UiWindowSurfaceRegistry new

3. registry bind with kind
   - Expected: elem.y equals `0`
   - Expected: elem.h equals `32`
   - Expected: elem.text equals `09:41`
   - Expected: elem.w equals `260`
   - Expected: elem.w equals `320`
   - Expected: elem.w equals `720`
   - Expected: elem.text equals `right`
   - Expected: right_icons equals `2`
   - Expected: launchers equals `2`
   - Expected: running equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 88 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = WindowManager.new()
val _opened = manager.open_window("surf1", "Terminal", 20, 40, 300, 200, _shared_tree("terminal"))
var registry = UiWindowSurfaceRegistry.new()
registry.bind_with_kind("win1", "surf1", 77u64, "simple.terminal", "Terminal", UI_SURFACE_KIND_SIMPLE_WEB)
val shared = shared_wm_scene_from_window_manager(manager, registry, 800, 600)

val scene = shared_wm_scene_to_chromed_wm_scene(shared, _shared_taskbar(), 1000, "09:41", 2)
val html = scene_to_html(scene)

var has_command = false
var has_clock = false
var right_icons = 0
var launchers = 0
var running = 0
var has_window_bar = false
var has_widgets = false
var has_control_center = false
var has_overview = false
var has_snap_preview = false
for elem in scene.elements:
    if elem.kind == "command_lane":
        has_command = true
        expect(elem.y).to_equal(0)
        expect(elem.h).to_equal(32)
    elif elem.kind == "command_clock":
        has_clock = true
        expect(elem.text).to_equal("09:41")
    elif elem.kind == "command_icon":
        right_icons = right_icons + 1
    elif elem.kind == "taskbar_launcher":
        launchers = launchers + 1
    elif elem.kind == "taskbar_running":
        running = running + 1
    elif elem.kind == "decoration":
        has_window_bar = true
    elif elem.kind == "desktop_widgets":
        has_widgets = true
        expect(elem.w).to_equal(260)
    elif elem.kind == "control_center":
        has_control_center = true
        expect(elem.w).to_equal(320)
    elif elem.kind == "window_overview":
        has_overview = true
        expect(elem.w).to_equal(720)
    elif elem.kind == "snap_preview":
        has_snap_preview = true
        expect(elem.text).to_equal("right")

expect(has_command)
expect(has_clock)
expect(right_icons).to_equal(2)
expect(launchers).to_equal(2)
expect(running).to_equal(1)
expect(has_window_bar)
expect(has_widgets)
expect(has_control_center)
expect(has_overview)
expect(has_snap_preview)
expect(html).to_contain("class='command-lane'")
expect(html).to_contain("data-app='terminal'")
expect(html).to_contain("data-window='win1'")
expect(html).to_contain("traffic-close")
expect(html).to_contain("bar-command")
expect(html).to_contain("aria-label='Desktop widgets'")
expect(html).to_contain("class='desktop-widget'")
expect(html).to_contain("aria-label='WM control center'")
expect(html).to_contain("data-motion-scope='control-center'")
expect(html).to_contain("data-motion-choice='standard'")
expect(html).to_contain("data-motion-choice='reduced'")
expect(html).to_contain("data-motion-choice='off'")
expect(html).to_contain("Standard motion")
expect(html).to_contain("Motion off")
expect(html).to_contain("aria-label='Window overview'")
expect(html).to_contain("class='overview-card active'")
expect(html).to_contain("class='snap-preview active'")
expect(html).to_contain("data-snap-zone='right'")
expect(html).to_contain("data-motion-mode='standard'")
expect(html).to_contain("data-motion-can-disable='true'")
expect(html).to_contain("data-reduced-motion-duration-ms='80'")
expect(html).to_contain("@keyframes wm-widget-float")
expect(html).to_contain("@keyframes wm-control-in")
expect(html).to_contain("@keyframes wm-overview-in")
expect(html).to_contain("@keyframes wm-snap-pulse")
expect(html).to_contain("@media (prefers-reduced-motion: reduce)")
expect(html).to_contain("body[data-motion-mode='reduced']")
expect(html).to_contain("body[data-motion-mode='off']")
expect(html).to_contain("animation:none!important")
expect(html).to_contain("repeat(auto-fit,minmax(180px,1fr))")
```

</details>

#### keeps modern chromed affordances bounded on compact scenes

1. var manager = WindowManager new

2. var registry = UiWindowSurfaceRegistry new
   - Expected: bounded_affordances equals `4`


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = WindowManager.new()
var registry = UiWindowSurfaceRegistry.new()
val shared = shared_wm_scene_from_window_manager(manager, registry, 240, 180)
val scene = shared_wm_scene_to_chromed_wm_scene(shared, _shared_taskbar(), 1000, "09:41", 1)

var bounded_affordances = 0
for elem in scene.elements:
    if elem.kind == "desktop_widgets" or elem.kind == "control_center" or elem.kind == "window_overview" or elem.kind == "snap_preview":
        bounded_affordances = bounded_affordances + 1
        expect(elem.x).to_be_greater_than(-1)
        expect(elem.y).to_be_greater_than(-1)
        expect(elem.w).to_be_greater_than(-1)
        expect(elem.h).to_be_greater_than(-1)
        expect(elem.x + elem.w).to_be_less_than(scene.width + 1)
        expect(elem.y + elem.h).to_be_less_than(scene.height + 1)

expect(bounded_affordances).to_equal(4)
```

</details>

#### reports visual quality metrics for rendered OS affordances

1. var manager = WindowManager new

2. var registry = UiWindowSurfaceRegistry new

3. registry bind with kind
   - Expected: report.max_control_center_width_px equals `320`
   - Expected: report.max_desktop_widget_width_px equals `260`
   - Expected: report.min_overview_card_width_px equals `180`
   - Expected: report.min_touch_target_height_px equals `36`
   - Expected: report.reduced_motion_duration_ms equals `80`


<details>
<summary>Executable SPipe</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = WindowManager.new()
val _opened = manager.open_window("surf1", "Terminal", 20, 40, 300, 200, _shared_tree("terminal"))
var registry = UiWindowSurfaceRegistry.new()
registry.bind_with_kind("win1", "surf1", 77u64, "simple.terminal", "Terminal", UI_SURFACE_KIND_SIMPLE_WEB)
val shared = shared_wm_scene_from_window_manager(manager, registry, 800, 600)
val scene = shared_wm_scene_to_chromed_wm_scene(shared, _shared_taskbar(), 1000, "09:41", 2)
val report = wm_scene_visual_quality_report(scene)

expect(report.passed)
expect(report.theme_configured)
expect(report.color_checked)
expect(report.contrast_ratio_x100).to_be_greater_than(449)
expect(report.bounded_layout)
expect(report.translucent_surfaces)
expect(report.rounded_surface_count).to_be_greater_than(3)
expect(report.max_control_center_width_px).to_equal(320)
expect(report.max_desktop_widget_width_px).to_equal(260)
expect(report.min_overview_card_width_px).to_equal(180)
expect(report.min_touch_target_height_px).to_equal(36)
expect(report.motion_can_disable)
expect(report.reduced_motion_duration_ms).to_equal(80)
```

</details>

#### fails visual quality when rendered affordances are out of bounds

1. SceneElement

2. SceneElement

3. SceneElement

4. SceneElement

5. SceneElement

6. expect not

7. expect not
   - Expected: report.max_control_center_width_px equals `340`
   - Expected: report.max_desktop_widget_width_px equals `280`


<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = WmSceneSpec(
    name: "bad_affordance_scene",
    width: 240,
    height: 180,
    elements: [
        SceneElement(kind: "desktop_chrome", x: 0, y: 0, w: 240, h: 180, color: 0xFF101418u32, text: ""),
        SceneElement(kind: "control_center", x: -4, y: 40, w: 340, h: 120, color: 0xDD111827u32, text: "oversized"),
        SceneElement(kind: "desktop_widgets", x: 20, y: 40, w: 280, h: 100, color: 0xCC111827u32, text: "oversized"),
        SceneElement(kind: "window_overview", x: 40, y: 72, w: 180, h: 80, color: 0xDD020617u32, text: "overview"),
        SceneElement(kind: "snap_preview", x: 120, y: 42, w: 130, h: 100, color: 0x552563EBu32, text: "right")
    ]
)
val report = wm_scene_visual_quality_report(scene)

expect_not(report.passed)
expect_not(report.bounded_layout)
expect(report.max_control_center_width_px).to_equal(340)
expect(report.max_desktop_widget_width_px).to_equal(280)
```

</details>

#### fails visual quality without modern affordance motion controls

1. expect not

2. expect not
   - Expected: report.reduced_motion_duration_ms equals `0`
   - Expected: report.min_touch_target_height_px equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(800, 600)
val report = wm_scene_visual_quality_report(scene)

expect_not(report.passed)
expect_not(report.motion_can_disable)
expect(report.reduced_motion_duration_ms).to_equal(0)
expect(report.min_touch_target_height_px).to_equal(0)
```

</details>

### WmScene — lifecycle motion projection

#### projects host-neutral lifecycle motion classes into inspectable HTML

1. WmLifecycleWindowState

2. WmLifecycleWindowState
   - Expected: opening_scene.name equals `lifecycle_motion_wm_scene`

3. expect not


<details>
<summary>Executable SPipe</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val windows = [
    WmLifecycleWindowState(id: 1, owner_port: 11, title: "Opening", x: 20, y: 60, w: 220, h: 160, content: "", process_id: 1, app_id: "/opening", minimized: false, focused: true),
    WmLifecycleWindowState(id: 2, owner_port: 22, title: "Hidden", x: 40, y: 80, w: 220, h: 160, content: "", process_id: 2, app_id: "/hidden", minimized: true, focused: false)
]
val opening_scene = lifecycle_windows_to_motion_wm_scene(windows, "create_window", 640, 480)
val opening_html = scene_to_html(opening_scene)
expect(opening_scene.name).to_equal("lifecycle_motion_wm_scene")
expect(opening_html).to_contain("class='motion-window wm-window-opening'")
expect(opening_html).to_contain("data-motion-phase='opening'")
expect(opening_html).to_contain("data-motion-duration-ms='240'")
expect(opening_html).to_contain("data-reduced-motion-duration-ms='80'")
expect(opening_html).to_contain("data-motion-can-disable='true'")
expect_not(opening_html.contains("Hidden"))

val minimizing_scene = lifecycle_windows_to_motion_wm_scene(windows, "minimize", 640, 480)
val minimizing_html = scene_to_html(minimizing_scene)
expect(minimizing_html).to_contain("wm-window-minimizing")
expect(minimizing_html).to_contain("data-title='Hidden'")
expect(minimizing_html).to_contain("data-motion-duration-ms='180'")

val restoring_scene = lifecycle_windows_to_motion_wm_scene(windows, "restore", 640, 480)
val restoring_html = scene_to_html(restoring_scene)
expect(restoring_html).to_contain("wm-window-restoring")
expect(restoring_html).to_contain("data-motion-phase='restoring'")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/compositor/wm_scene_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WmScene — standard_wm_scene
- WmScene — render_scene_to_backend
- WmScene — scene_to_html
- WmScene — SharedWmScene projection
- WmScene — lifecycle motion projection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
