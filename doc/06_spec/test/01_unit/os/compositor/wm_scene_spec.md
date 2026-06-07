# Wm Scene Specification

> <details>

<!-- sdn-diagram:id=wm_scene_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_scene_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_scene_spec -> std
wm_scene_spec -> os
wm_scene_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_scene_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Scene Specification

## Scenarios

### WmScene — standard_wm_scene

#### scene structure

#### AC-2: standard scene has correct dimensions

<details>
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

Runnable source: 55 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = standard_wm_scene(W, H)
val html = scene_to_html(scene)
expect(html).to_contain("data-modern-wm='true'")
expect(html).to_contain("data-theme-configured='true'")
expect(html).to_contain("data-window-radius-px='18'")
expect(html).to_contain("data-widget-radius-px='14'")
expect(html).to_contain("data-taskbar-radius-px='999'")
expect(html).to_contain("data-icon-radius-px='999'")
expect(html).to_contain("data-icon-inner-padding-px='3'")
expect(html).to_contain("data-icon-mask-shape='circle'")
expect(html).to_contain("data-icon-image-fit='cover'")
expect(html).to_contain("data-layout-safe-area-px='16'")
expect(html).to_contain("data-layout-panel-gap-px='12'")
expect(html).to_contain("data-layout-min-touch-target-px='44'")
expect(html).to_contain("data-layout-containment='layout-paint'")
expect(html).to_contain("data-layout-contained='true'")
expect(html).to_contain("[data-layout-contained='true']{{contain:layout paint")
expect(html).to_contain(".wm-panel{{box-sizing:border-box;overflow:hidden;min-height:44px")
expect(html).to_contain("data-material-policy='glass-vibrancy'")
expect(html).to_contain("data-glass-blur-px='24'")
expect(html).to_contain("data-glass-saturation-pct='170'")
expect(html).to_contain("data-glass-opacity-floor-x100='6'")
expect(html).to_contain("data-blur-px='24'")
expect(html).to_contain("data-scrollbar-width-px='10'")
expect(html).to_contain("data-scrollbar-thumb-radius-px='999'")
expect(html).to_contain("data-scrollbar-thumb-border-px='3'")
expect(html).to_contain("scrollbar-width:thin")
expect(html).to_contain("::-webkit-scrollbar-thumb")
expect(html).to_contain("background-clip:padding-box")
expect(html).to_contain("data-desktop-layer-z='0'")
expect(html).to_contain("data-window-layer-z='20'")
expect(html).to_contain("data-overlay-layer-z='11000'")
expect(html).to_contain("data-standard-motion-ms='240'")
expect(html).to_contain("data-reduced-motion-ms='80'")
expect(html).to_contain("<button class='traffic traffic-close'")
expect(html).to_contain("data-window-control='close'")
expect(html).to_contain("aria-label='Close window'")
expect(html).to_contain("<button class='traffic traffic-min'")
expect(html).to_contain("data-window-control='minimize'")
expect(html).to_contain("aria-label='Minimize window'")
expect(html).to_contain("<button class='traffic traffic-max'")
expect(html).to_contain("data-window-control='maximize'")
expect(html).to_contain("aria-label='Maximize window'")
expect(html).to_contain(".traffic::before")
expect(html).to_contain("inset:-8px")
expect(html).to_contain(".traffic:focus-visible")
expect(html).to_contain("<input class='bar-command-input'")
expect(html).to_contain("aria-label='Window command or location'")
expect(html).to_contain(".bar-command-input{{min-width:140px")
expect(html).to_contain(".bar-command-input:focus")
expect(html).to_contain("bar-context")
expect(html).to_contain("border-radius:18px 18px 0 0")
expect(html).to_contain("border-radius:999px")
expect(html).to_contain("radial-gradient")
expect(html).to_contain("backdrop-filter:blur(24px)")
```

</details>

#### AC-2: exposes a deterministic modern theme configuration for OS renderers

<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
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
expect(config.icon_inner_padding_px).to_equal(3)
expect(config.icon_mask_shape).to_equal("circle")
expect(config.icon_image_fit).to_equal("cover")
expect(config.layout_safe_area_px).to_equal(16)
expect(config.layout_panel_gap_px).to_equal(12)
expect(config.layout_min_touch_target_px).to_equal(44)
expect(config.layout_containment).to_equal("layout-paint")
expect(config.scrollbar_width_px).to_equal(10)
expect(config.scrollbar_thumb_radius_px).to_equal(999)
expect(config.scrollbar_thumb_border_px).to_equal(3)
expect(config.blur_px).to_equal(24)
expect(config.glass_saturation_pct).to_equal(170)
expect(config.glass_opacity_floor_x100).to_equal(6)
expect(config.material_policy).to_equal("glass-vibrancy")
expect(config.desktop_layer_z).to_equal(0)
expect(config.snap_layer_z).to_equal(15)
expect(config.window_layer_z).to_equal(20)
expect(config.overlay_layer_z).to_equal(11000)
expect(config.standard_motion_ms).to_equal(240)
expect(config.reduced_motion_ms).to_equal(80)
expect(config.can_disable_motion)
```

</details>

#### AC-2: classifies OS compositor icons for round normalization

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wm_scene_icon_kind("https://simple.local/icon.png")).to_equal("square-to-round")
expect(wm_scene_icon_kind("data:image/gif;base64,R0lGODlhAQABAAAAACw=")).to_equal("square-to-round")
expect(wm_scene_icon_kind("/apps/simple.png")).to_equal("square-to-round")
expect(wm_scene_icon_kind("terminal")).to_equal("glyph-to-round")
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
<summary>Executable SSpec</summary>

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
   - Expected: elem.w equals `680`
   - Expected: elem.w equals `320`
   - Expected: elem.w equals `720`
   - Expected: elem.text equals `right`
   - Expected: elem.w equals `360`
   - Expected: elem.text equals `Window snapped|Right half|Undo`
   - Expected: elem.w equals `340`
   - Expected: elem.text equals `Window snapped|Build finished|Calendar`
   - Expected: elem.w equals `420`
   - Expected: elem.text equals `Build indexing|72|Pause|Cancel`
   - Expected: elem.w equals `360`
   - Expected: elem.text equals `1|2|3`
   - Expected: elem.w equals `420`
   - Expected: elem.text equals `Keyboard shortcuts`
   - Expected: elem.w equals `520`
   - Expected: elem.text equals `Terminal|Browser|Simple IDE|Settings`
   - Expected: elem.w equals `280`
   - Expected: elem.text equals `Open|Pin to taskbar|Move to workspace|Close`
   - Expected: elem.w equals `360`
   - Expected: elem.text equals `Left half|Right half|Fullscreen|Quarter grid`
   - Expected: elem.w equals `460`
   - Expected: elem.text equals `Terminal|Browser|Settings`
   - Expected: elem.w equals `300`
   - Expected: elem.text equals `Wi-Fi|Audio|Battery|Brightness`
   - Expected: elem.w equals `44`
   - Expected: elem.h equals `44`
   - Expected: elem.w equals `240`
   - Expected: elem.h equals `64`
   - Expected: elem.text equals `300 x 200|20,40|Snap ready`
   - Expected: elem.w equals `360`
   - Expected: elem.text equals `Swipe up|Pinch out|Swipe left`
   - Expected: elem.w equals `320`
   - Expected: elem.text equals `Terminal|simple.terminal|win1`
   - Expected: elem.w equals `88`
   - Expected: elem.text equals `Terminal|Browser|Settings`
   - Expected: elem.w equals `560`
   - Expected: elem.text equals `Selection|Window|Screen|Capture`
   - Expected: elem.w equals `360`
   - Expected: elem.text equals `Command|Code|Link|Paste|Pin|Clear`
   - Expected: right_icons equals `2`
   - Expected: launchers equals `2`
   - Expected: running equals `1`
   - Expected: hot_corner_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 594 lines folded for reproduction.
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
var has_command_palette = false
var has_control_center = false
var has_overview = false
var has_snap_preview = false
var has_notification = false
var has_notification_center = false
var has_live_activity = false
var has_workspace_switcher = false
var has_shortcut_overlay = false
var has_app_launcher = false
var has_context_menu = false
var has_snap_layouts = false
var has_window_switcher = false
var has_quick_settings = false
var hot_corner_count = 0
var has_resize_hud = false
var has_gesture_hints = false
var has_taskbar_preview = false
var has_stage_rail = false
var has_screen_capture = false
var has_clipboard_history = false
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
    elif elem.kind == "command_palette":
        has_command_palette = true
        expect(elem.w).to_equal(680)
    elif elem.kind == "control_center":
        has_control_center = true
        expect(elem.w).to_equal(320)
    elif elem.kind == "window_overview":
        has_overview = true
        expect(elem.w).to_equal(720)
    elif elem.kind == "snap_preview":
        has_snap_preview = true
        expect(elem.text).to_equal("right")
    elif elem.kind == "notification_toast":
        has_notification = true
        expect(elem.w).to_equal(360)
        expect(elem.text).to_equal("Window snapped|Right half|Undo")
    elif elem.kind == "notification_center":
        has_notification_center = true
        expect(elem.w).to_equal(340)
        expect(elem.text).to_equal("Window snapped|Build finished|Calendar")
    elif elem.kind == "live_activity":
        has_live_activity = true
        expect(elem.w).to_equal(420)
        expect(elem.text).to_equal("Build indexing|72|Pause|Cancel")
    elif elem.kind == "workspace_switcher":
        has_workspace_switcher = true
        expect(elem.w).to_equal(360)
        expect(elem.text).to_equal("1|2|3")
    elif elem.kind == "shortcut_overlay":
        has_shortcut_overlay = true
        expect(elem.w).to_equal(420)
        expect(elem.text).to_equal("Keyboard shortcuts")
    elif elem.kind == "app_launcher":
        has_app_launcher = true
        expect(elem.w).to_equal(520)
        expect(elem.text).to_equal("Terminal|Browser|Simple IDE|Settings")
    elif elem.kind == "context_menu":
        has_context_menu = true
        expect(elem.w).to_equal(280)
        expect(elem.text).to_equal("Open|Pin to taskbar|Move to workspace|Close")
    elif elem.kind == "snap_layouts":
        has_snap_layouts = true
        expect(elem.w).to_equal(360)
        expect(elem.text).to_equal("Left half|Right half|Fullscreen|Quarter grid")
    elif elem.kind == "window_switcher":
        has_window_switcher = true
        expect(elem.w).to_equal(460)
        expect(elem.text).to_equal("Terminal|Browser|Settings")
    elif elem.kind == "quick_settings":
        has_quick_settings = true
        expect(elem.w).to_equal(300)
        expect(elem.text).to_equal("Wi-Fi|Audio|Battery|Brightness")
    elif elem.kind == "hot_corner_zone":
        hot_corner_count = hot_corner_count + 1
        expect(elem.w).to_equal(44)
        expect(elem.h).to_equal(44)
    elif elem.kind == "resize_hud":
        has_resize_hud = true
        expect(elem.w).to_equal(240)
        expect(elem.h).to_equal(64)
        expect(elem.text).to_equal("300 x 200|20,40|Snap ready")
    elif elem.kind == "gesture_hints":
        has_gesture_hints = true
        expect(elem.w).to_equal(360)
        expect(elem.text).to_equal("Swipe up|Pinch out|Swipe left")
    elif elem.kind == "taskbar_preview":
        has_taskbar_preview = true
        expect(elem.w).to_equal(320)
        expect(elem.text).to_equal("Terminal|simple.terminal|win1")
    elif elem.kind == "stage_rail":
        has_stage_rail = true
        expect(elem.w).to_equal(88)
        expect(elem.text).to_equal("Terminal|Browser|Settings")
    elif elem.kind == "screen_capture_overlay":
        has_screen_capture = true
        expect(elem.w).to_equal(560)
        expect(elem.text).to_equal("Selection|Window|Screen|Capture")
    elif elem.kind == "clipboard_history":
        has_clipboard_history = true
        expect(elem.w).to_equal(360)
        expect(elem.text).to_equal("Command|Code|Link|Paste|Pin|Clear")

expect(has_command)
expect(has_clock)
expect(right_icons).to_equal(2)
expect(launchers).to_equal(2)
expect(running).to_equal(1)
expect(has_window_bar)
expect(has_widgets)
expect(has_command_palette)
expect(has_control_center)
expect(has_overview)
expect(has_snap_preview)
expect(has_notification)
expect(has_notification_center)
expect(has_live_activity)
expect(has_workspace_switcher)
expect(has_shortcut_overlay)
expect(has_app_launcher)
expect(has_context_menu)
expect(has_snap_layouts)
expect(has_window_switcher)
expect(has_quick_settings)
expect(hot_corner_count).to_equal(4)
expect(has_resize_hud)
expect(has_gesture_hints)
expect(has_taskbar_preview)
expect(has_stage_rail)
expect(has_screen_capture)
expect(has_clipboard_history)
expect(html).to_contain("class='command-lane'")
expect(html).to_contain("data-app='terminal'")
expect(html).to_contain("data-window='win1'")
expect(html).to_contain("data-taskbar-motion='dock-hover'")
expect(html).to_contain("data-taskbar-state='running'")
expect(html).to_contain("aria-label='Launch terminal'")
expect(html).to_contain("aria-label='Focus window win1'")
expect(html).to_contain("class='taskbar-running-indicator'")
expect(html).to_contain("data-dock-magnification='1.18'")
expect(html).to_contain("data-dock-neighbor-magnification='1.07'")
expect(html).to_contain(".taskbar-launcher:hover,.taskbar-running:hover")
expect(html).to_contain("transform:translateY(-6px) scale(1.18)")
expect(html).to_contain(".taskbar-launcher:hover + .taskbar-launcher")
expect(html).to_contain(".taskbar-running:hover + .taskbar-running")
expect(html).to_contain("scale(1.07)")
expect(html).to_contain("filter:brightness(1.12)")
expect(html).to_contain("outline-offset:3px;transform:translateY(-6px) scale(1.18)")
expect(html).to_contain(".taskbar-launcher:focus-visible,.taskbar-running:focus-visible")
expect(html).to_contain("@keyframes wm-taskbar-indicator")
expect(html).to_contain("body[data-motion-mode='reduced'] .taskbar-running-indicator")
expect(html).to_contain("body[data-motion-mode='off'] .taskbar-running-indicator")
expect(html).to_contain("data-window-focus='focused'")
expect(html).to_contain("data-elevation-layer='active-window'")
expect(html).to_contain("class='bar focused'")
expect(html).to_contain("class='glass focused'")
expect(html).to_contain(".bar.focused")
expect(html).to_contain(".glass.focused")
expect(html).to_contain("transform:translateY(-1px)")
expect(html).to_contain("data-icon-normalized='square-to-round'")
expect(html).to_contain("data-icon-normalized='glyph-to-round'")
expect(html).to_contain("icon-normalized-square")
expect(html).to_contain("icon-glyph-to-round")
expect(html).to_contain("icon-image-placeholder")
expect(html).to_contain("clip-path:circle(50% at 50% 50%)")
expect(html).to_contain("data-icon-mask='circle'")
expect(html).to_contain("data-icon-fit='cover'")
expect(html).to_contain("data-icon-fit='glyph'")
expect(html).to_contain("data-icon-fallback='")
expect(html).to_contain("aria-label='Normalized round icon")
expect(html).to_contain("aria-label='Round glyph icon")
expect(html).to_contain(".round-icon.icon-normalized-square{{padding:3px")
expect(html).to_contain("object-position:center")
expect(html).to_contain("aspect-ratio:1 / 1")
expect(html).to_contain(".round-icon.icon-glyph-to-round{{text-transform:uppercase")
expect(html).to_contain("<button class='traffic traffic-close'")
expect(html).to_contain("data-window-control='close'")
expect(html).to_contain("data-window-control='minimize'")
expect(html).to_contain("data-window-control='maximize'")
expect(html).to_contain("<input class='bar-command-input'")
expect(html).to_contain("aria-label='Window command or location'")
expect(html).to_contain("data-drag-region='titlebar'")
expect(html).to_contain("data-drag-hit-size-px='44'")
expect(html).to_contain("data-resize-surface='window'")
expect(html).to_contain("class='resize-handle resize-east'")
expect(html).to_contain("class='resize-handle resize-south'")
expect(html).to_contain("class='resize-handle resize-west'")
expect(html).to_contain("class='resize-handle resize-south-east'")
expect(html).to_contain("data-resize-edge='south-east'")
expect(html).to_contain("data-hit-size-px='44'")
expect(html).to_contain(".resize-handle::before")
expect(html).to_contain(".resize-handle:focus-visible")
expect(html).to_contain("aria-label='Desktop widgets'")
expect(html).to_contain("class='desktop-widget'")
expect(html).to_contain("role='dialog' aria-label='Simple command palette'")
expect(html).to_contain("data-motion-scope='command-palette'")
expect(html).to_contain("class='command-palette-input'")
expect(html).to_contain("aria-label='Global command'")
expect(html).to_contain("class='command-palette-list' role='listbox'")
expect(html).to_contain("class='command-palette-item active' role='option' aria-selected='true'")
expect(html).to_contain("Open Simple IDE")
expect(html).to_contain("Show window overview")
expect(html).to_contain("@keyframes wm-command-in")
expect(html).to_contain("body[data-motion-mode='reduced'] .command-palette")
expect(html).to_contain("body[data-motion-mode='off'] .command-palette")
expect(html).to_contain("aria-label='WM control center'")
expect(html).to_contain("data-motion-scope='desktop-background'")
expect(html).to_contain(".desktop::before")
expect(html).to_contain("@keyframes wm-bg-drift")
expect(html).to_contain("animation:wm-bg-drift")
expect(html).to_contain("data-motion-scope='control-center'")
expect(html).to_contain("data-motion-choice='standard'")
expect(html).to_contain("data-motion-choice='reduced'")
expect(html).to_contain("data-motion-choice='off'")
expect(html).to_contain("class='accent-controls' role='group' aria-label='Theme accent color'")
expect(html).to_contain("class='accent-swatch active' data-accent-choice='blue'")
expect(html).to_contain("data-accent-choice='teal'")
expect(html).to_contain("data-accent-choice='rose'")
expect(html).to_contain("aria-label='Use blue accent'")
expect(html).to_contain(".accent-swatch[data-accent-choice='blue']")
expect(html).to_contain(".accent-swatch:focus-visible")
expect(html).to_contain("Standard motion")
expect(html).to_contain("Motion off")
expect(html).to_contain("aria-label='Window overview'")
expect(html).to_contain("class='overview-card active'")
expect(html).to_contain("class='snap-preview active'")
expect(html).to_contain("data-snap-zone='right'")
expect(html).to_contain("class='notification-toast toast-enter'")
expect(html).to_contain("role='status' aria-live='polite'")
expect(html).to_contain("data-motion-scope='notification-toast'")
expect(html).to_contain("data-toast-state='entering'")
expect(html).to_contain("Window snapped")
expect(html).to_contain("Right half")
expect(html).to_contain("class='toast-action' aria-label='Undo notification action'")
expect(html).to_contain("class='toast-progress'")
expect(html).to_contain("max-width:360px")
expect(html).to_contain("class='notification-center'")
expect(html).to_contain("role='dialog' aria-label='Notification center'")
expect(html).to_contain("data-motion-scope='notification-center'")
expect(html).to_contain("data-notification-source='history'")
expect(html).to_contain("class='notification-clear' aria-label='Clear notifications'")
expect(html).to_contain("class='notification-list' role='list'")
expect(html).to_contain("class='notification-card unread' role='listitem' data-notification-kind='window'")
expect(html).to_contain("data-notification-kind='build'")
expect(html).to_contain("data-notification-kind='calendar'")
expect(html).to_contain("Build finished")
expect(html).to_contain("Focus block starts soon")
expect(html).to_contain("@keyframes wm-notification-center-in")
expect(html).to_contain("body[data-motion-mode='reduced'] .notification-center")
expect(html).to_contain("body[data-motion-mode='off'] .notification-center")
expect(html).to_contain("class='live-activity'")
expect(html).to_contain("role='status' aria-live='polite' aria-label='Live activity'")
expect(html).to_contain("data-motion-scope='live-activity'")
expect(html).to_contain("data-live-activity='build-indexing'")
expect(html).to_contain("class='live-activity-copy'")
expect(html).to_contain("72% complete")
expect(html).to_contain("class='live-activity-progress' role='progressbar'")
expect(html).to_contain("aria-valuenow='72'")
expect(html).to_contain("data-live-action='pause'")
expect(html).to_contain("data-live-action='cancel'")
expect(html).to_contain("@keyframes wm-live-activity-in")
expect(html).to_contain("@keyframes wm-live-activity-progress")
expect(html).to_contain("body[data-motion-mode='reduced'] .live-activity")
expect(html).to_contain("body[data-motion-mode='off'] .live-activity")
expect(html).to_contain("class='workspace-switcher'")
expect(html).to_contain("role='tablist' aria-label='Workspaces'")
expect(html).to_contain("data-motion-scope='workspace-switcher'")
expect(html).to_contain("class='workspace-active-pill'")
expect(html).to_contain("class='workspace-tab active' role='tab' aria-selected='true' data-workspace-id='1'")
expect(html).to_contain("aria-label='Switch to workspace 1'")
expect(html).to_contain("data-workspace-id='2'")
expect(html).to_contain("data-workspace-id='3'")
expect(html).to_contain("Meta 1")
expect(html).to_contain("class='shortcut-overlay'")
expect(html).to_contain("role='dialog' aria-label='Keyboard shortcuts'")
expect(html).to_contain("data-motion-scope='shortcut-overlay'")
expect(html).to_contain("class='shortcut-header'")
expect(html).to_contain("class='shortcut-close' aria-label='Close keyboard shortcuts'")
expect(html).to_contain("class='shortcut-grid'")
expect(html).to_contain("class='shortcut-row'")
expect(html).to_contain("Command palette")
expect(html).to_contain("Meta K")
expect(html).to_contain("Window overview")
expect(html).to_contain("Meta O")
expect(html).to_contain("Control center")
expect(html).to_contain("Meta ,")
expect(html).to_contain("Switch workspace")
expect(html).to_contain("Meta 1-3")
expect(html).to_contain("Snap window")
expect(html).to_contain("Meta Arrow")
expect(html).to_contain("max-width:420px")
expect(html).to_contain("data-motion-mode='standard'")
expect(html).to_contain("data-motion-can-disable='true'")
expect(html).to_contain("data-reduced-motion-duration-ms='80'")
expect(html).to_contain("@keyframes wm-widget-float")
expect(html).to_contain("@keyframes wm-control-in")
expect(html).to_contain("@keyframes wm-overview-in")
expect(html).to_contain("@keyframes wm-snap-pulse")
expect(html).to_contain("@keyframes wm-toast-in")
expect(html).to_contain("@keyframes wm-toast-out")
expect(html).to_contain("@keyframes wm-toast-progress")
expect(html).to_contain("@keyframes wm-workspace-in")
expect(html).to_contain("@keyframes wm-workspace-slide")
expect(html).to_contain("@keyframes wm-shortcut-in")
expect(html).to_contain("@media (prefers-reduced-motion: reduce)")
expect(html).to_contain("body[data-motion-mode='reduced']")
expect(html).to_contain("body[data-motion-mode='reduced'] .desktop::before")
expect(html).to_contain("body[data-motion-mode='off']")
expect(html).to_contain("body[data-motion-mode='off'] .desktop::before")
expect(html).to_contain("body[data-motion-mode='reduced'] .notification-toast")
expect(html).to_contain("body[data-motion-mode='off'] .notification-toast")
expect(html).to_contain("body[data-motion-mode='off'] .toast-progress")
expect(html).to_contain("body[data-motion-mode='reduced'] .workspace-switcher")
expect(html).to_contain("body[data-motion-mode='off'] .workspace-switcher")
expect(html).to_contain("body[data-motion-mode='off'] .workspace-active-pill")
expect(html).to_contain("body[data-motion-mode='reduced'] .shortcut-overlay")
expect(html).to_contain("body[data-motion-mode='off'] .shortcut-overlay")
expect(html).to_contain("animation:none!important")
expect(html).to_contain("repeat(auto-fit,minmax(180px,1fr))")
expect(html).to_contain("class='app-launcher'")
expect(html).to_contain("role='dialog' aria-label='App launcher'")
expect(html).to_contain("class='app-launcher-search'")
expect(html).to_contain("class='app-launcher-grid' role='listbox'")
expect(html).to_contain("data-app-id='terminal'")
expect(html).to_contain("data-app-id='browser'")
expect(html).to_contain("data-app-id='simple-ide'")
expect(html).to_contain("data-app-id='settings'")
expect(html).to_contain("@keyframes wm-launcher-in")
expect(html).to_contain("body[data-motion-mode='reduced'] .app-launcher")
expect(html).to_contain("body[data-motion-mode='off'] .app-launcher")
expect(html).to_contain("repeat(auto-fit,minmax(96px,1fr))")
expect(html).to_contain("class='context-menu'")
expect(html).to_contain("role='menu' aria-label='Window context menu'")
expect(html).to_contain("data-context-target='win1'")
expect(html).to_contain("class='context-menu-item active' role='menuitem' data-command='open'")
expect(html).to_contain("role='menuitemcheckbox' aria-checked='false' data-command='pin-to-taskbar'")
expect(html).to_contain("class='context-menu-separator' role='separator'")
expect(html).to_contain("data-command='move-to-workspace'")
expect(html).to_contain("class='context-menu-item danger' role='menuitem' data-command='close'")
expect(html).to_contain("@keyframes wm-menu-in")
expect(html).to_contain("body[data-motion-mode='reduced'] .context-menu")
expect(html).to_contain("body[data-motion-mode='off'] .context-menu")
expect(html).to_contain("class='snap-layouts'")
expect(html).to_contain("role='dialog' aria-label='Snap layouts'")
expect(html).to_contain("data-motion-scope='snap-layouts'")
expect(html).to_contain("data-snap-layout-target='win1'")
expect(html).to_contain("class='snap-layout-option active' role='option' aria-selected='true' data-snap-layout='left-half'")
expect(html).to_contain("data-snap-layout='right-half'")
expect(html).to_contain("data-snap-layout='fullscreen'")
expect(html).to_contain("data-snap-layout='quarter-grid'")
expect(html).to_contain("class='snap-layout-diagram split-left'")
expect(html).to_contain("class='snap-layout-diagram split-right'")
expect(html).to_contain("class='snap-layout-diagram fullscreen'")
expect(html).to_contain("class='snap-layout-diagram quarter-grid'")
expect(html).to_contain("Meta Arrow")
expect(html).to_contain("@keyframes wm-snap-layouts-in")
expect(html).to_contain("body[data-motion-mode='reduced'] .snap-layouts")
expect(html).to_contain("body[data-motion-mode='off'] .snap-layouts")
expect(html).to_contain("class='window-switcher'")
expect(html).to_contain("role='dialog' aria-label='Window switcher'")
expect(html).to_contain("data-motion-scope='window-switcher'")
expect(html).to_contain("data-switcher-shortcut='Meta Tab'")
expect(html).to_contain("class='window-switcher-list' role='listbox'")
expect(html).to_contain("class='window-switcher-item active' role='option' aria-selected='true' data-switch-window='win1'")
expect(html).to_contain("data-switch-window='win2'")
expect(html).to_contain("data-switch-window='win3'")
expect(html).to_contain("window-switcher-icon")
expect(html).to_contain("Switch windows")
expect(html).to_contain("Meta Tab")
expect(html).to_contain("@keyframes wm-switcher-in")
expect(html).to_contain("body[data-motion-mode='reduced'] .window-switcher")
expect(html).to_contain("body[data-motion-mode='off'] .window-switcher")
expect(html).to_contain("class='quick-settings'")
expect(html).to_contain("role='dialog' aria-label='Quick settings'")
expect(html).to_contain("data-motion-scope='quick-settings'")
expect(html).to_contain("data-command-lane-source='right-icons'")
expect(html).to_contain("class='quick-settings-grid'")
expect(html).to_contain("data-setting='wifi' aria-pressed='true'")
expect(html).to_contain("data-setting='audio' aria-pressed='true'")
expect(html).to_contain("data-setting='battery' aria-pressed='false'")
expect(html).to_contain("data-setting='brightness' aria-pressed='false'")
expect(html).to_contain("Office")
expect(html).to_contain("42%")
expect(html).to_contain("86%")
expect(html).to_contain("68%")
expect(html).to_contain("quick-setting-icon")
expect(html).to_contain("@keyframes wm-quick-settings-in")
expect(html).to_contain("body[data-motion-mode='reduced'] .quick-settings")
expect(html).to_contain("body[data-motion-mode='off'] .quick-settings")
expect(html).to_contain("class='hot-corner-zone hot-corner-overview'")
expect(html).to_contain("class='hot-corner-zone hot-corner-launcher'")
expect(html).to_contain("class='hot-corner-zone hot-corner-desktop'")
expect(html).to_contain("class='hot-corner-zone hot-corner-control-center'")
expect(html).to_contain("data-hot-corner-action='overview'")
expect(html).to_contain("data-hot-corner-action='launcher'")
expect(html).to_contain("data-hot-corner-action='desktop'")
expect(html).to_contain("data-hot-corner-action='control-center'")
expect(html).to_contain("class='hot-corner-ring'")
expect(html).to_contain("@keyframes wm-hot-corner-pulse")
expect(html).to_contain("body[data-motion-mode='reduced'] .hot-corner-ring")
expect(html).to_contain("body[data-motion-mode='off'] .hot-corner-ring")
expect(html).to_contain("class='resize-hud'")
expect(html).to_contain("role='status' aria-live='polite'")
expect(html).to_contain("aria-label='Window resize feedback'")
expect(html).to_contain("data-resize-state='active'")
expect(html).to_contain("class='resize-hud-size'")
expect(html).to_contain("300 x 200")
expect(html).to_contain("class='resize-hud-position'")
expect(html).to_contain("20,40")
expect(html).to_contain("class='resize-hud-snap'")
expect(html).to_contain("Snap ready")
expect(html).to_contain("@keyframes wm-resize-hud-in")
expect(html).to_contain("body[data-motion-mode='reduced'] .resize-hud")
expect(html).to_contain("body[data-motion-mode='off'] .resize-hud")
expect(html).to_contain("class='gesture-hints'")
expect(html).to_contain("aria-label='Trackpad gesture hints'")
expect(html).to_contain("data-motion-scope='gesture-hints'")
expect(html).to_contain("class='gesture-hint-list'")
expect(html).to_contain("data-gesture='swipe-up'")
expect(html).to_contain("Swipe up")
expect(html).to_contain("data-gesture='pinch-out'")
expect(html).to_contain("Pinch out")
expect(html).to_contain("data-gesture='swipe-left'")
expect(html).to_contain("Swipe left")
expect(html).to_contain("@keyframes wm-gesture-hints-in")
expect(html).to_contain("body[data-motion-mode='reduced'] .gesture-hints")
expect(html).to_contain("body[data-motion-mode='off'] .gesture-hints")
expect(html).to_contain("class='taskbar-preview'")
expect(html).to_contain("role='tooltip' aria-label='Taskbar window preview'")
expect(html).to_contain("data-motion-scope='taskbar-preview'")
expect(html).to_contain("data-preview-window='win1'")
expect(html).to_contain("class='taskbar-preview-thumb'")
expect(html).to_contain("class='taskbar-preview-titlebar'")
expect(html).to_contain("class='taskbar-preview-body'")
expect(html).to_contain("class='taskbar-preview-meta'")
expect(html).to_contain("simple.terminal")
expect(html).to_contain("class='taskbar-preview-focus' aria-label='Focus preview window win1'")
expect(html).to_contain("@keyframes wm-taskbar-preview-in")
expect(html).to_contain("body[data-motion-mode='reduced'] .taskbar-preview")
expect(html).to_contain("body[data-motion-mode='off'] .taskbar-preview")
expect(html).to_contain("class='stage-rail'")
expect(html).to_contain("aria-label='Window stage rail'")
expect(html).to_contain("data-motion-scope='stage-rail'")
expect(html).to_contain("class='stage-rail-item active'")
expect(html).to_contain("data-stage-window='win1'")
expect(html).to_contain("data-stage-window='win2'")
expect(html).to_contain("data-stage-window='win3'")
expect(html).to_contain("class='stage-rail-thumb'")
expect(html).to_contain("Activate Terminal stage")
expect(html).to_contain("@keyframes wm-stage-rail-in")
expect(html).to_contain("body[data-motion-mode='reduced'] .stage-rail")
expect(html).to_contain("body[data-motion-mode='off'] .stage-rail")
expect(html).to_contain("class='screen-capture-overlay'")
expect(html).to_contain("role='dialog' aria-label='Screen capture'")
expect(html).to_contain("data-motion-scope='screen-capture'")
expect(html).to_contain("data-capture-mode='selection'")
expect(html).to_contain("class='capture-selection' role='img' aria-label='Selected capture region 420 by 160'")
expect(html).to_contain("class='capture-handle nw' data-capture-handle='nw'")
expect(html).to_contain("class='capture-handle ne' data-capture-handle='ne'")
expect(html).to_contain("class='capture-handle sw' data-capture-handle='sw'")
expect(html).to_contain("class='capture-handle se' data-capture-handle='se'")
expect(html).to_contain("class='capture-dimensions'")
expect(html).to_contain("420 x 160")
expect(html).to_contain("class='capture-toolbar' role='toolbar' aria-label='Capture controls'")
expect(html).to_contain("class='capture-mode active' data-capture-mode='selection' aria-pressed='true'")
expect(html).to_contain("data-capture-mode='window'")
expect(html).to_contain("data-capture-mode='screen'")
expect(html).to_contain("data-capture-action='capture'")
expect(html).to_contain("@keyframes wm-capture-in")
expect(html).to_contain("body[data-motion-mode='reduced'] .screen-capture-overlay")
expect(html).to_contain("body[data-motion-mode='off'] .screen-capture-overlay")
expect(html).to_contain("class='clipboard-history' role='dialog' aria-label='Clipboard history'")
expect(html).to_contain("data-motion-scope='clipboard-history'")
expect(html).to_contain("data-clipboard-source='system'")
expect(html).to_contain("class='clipboard-clear' data-clipboard-action='clear'")
expect(html).to_contain("class='clipboard-list' role='listbox'")
expect(html).to_contain("class='clipboard-item active' role='option' aria-selected='true' data-clipboard-kind='command'")
expect(html).to_contain("data-clipboard-kind='code'")
expect(html).to_contain("class='clipboard-item pinned'")
expect(html).to_contain("data-clipboard-kind='link'")
expect(html).to_contain("data-clipboard-action='paste'")
expect(html).to_contain("class='clipboard-pin' data-clipboard-action='pin'")
expect(html).to_contain("@keyframes wm-clipboard-in")
expect(html).to_contain("body[data-motion-mode='reduced'] .clipboard-history")
expect(html).to_contain("body[data-motion-mode='off'] .clipboard-history")
expect(html).to_contain("class='privacy-indicator'")
expect(html).to_contain("role='status' aria-live='polite' aria-label='Privacy activity'")
expect(html).to_contain("data-motion-scope='privacy-indicator'")
expect(html).to_contain("data-privacy-source='system-services'")
expect(html).to_contain("class='privacy-dot camera'")
expect(html).to_contain("Camera active")
expect(html).to_contain("Mic active")
expect(html).to_contain("Screen sharing")
expect(html).to_contain("class='privacy-actions' role='group' aria-label='Privacy controls'")
expect(html).to_contain("data-privacy-action='allow'")
expect(html).to_contain("data-privacy-action='block'")
expect(html).to_contain("@keyframes wm-privacy-in")
expect(html).to_contain("@keyframes wm-privacy-pulse")
expect(html).to_contain("body[data-motion-mode='reduced'] .privacy-indicator")
expect(html).to_contain("body[data-motion-mode='off'] .privacy-indicator")
expect(html).to_contain("class='system-hud'")
expect(html).to_contain("role='status' aria-live='polite' aria-label='System volume and brightness'")
expect(html).to_contain("data-motion-scope='system-hud'")
expect(html).to_contain("data-hud-source='hardware-keys'")
expect(html).to_contain("class='system-hud-meter' role='meter' aria-label='Volume level'")
expect(html).to_contain("aria-valuenow='68'")
expect(html).to_contain("data-hud-action='mute'")
expect(html).to_contain("data-hud-action='brightness'")
expect(html).to_contain("@keyframes wm-system-hud-in")
expect(html).to_contain("body[data-motion-mode='reduced'] .system-hud")
expect(html).to_contain("body[data-motion-mode='off'] .system-hud")
expect(html).to_contain("class='wallpaper-picker'")
expect(html).to_contain("role='dialog' aria-label='Wallpaper picker'")
expect(html).to_contain("data-motion-scope='wallpaper-picker'")
expect(html).to_contain("data-wallpaper-source='desktop-background'")
expect(html).to_contain("class='wallpaper-dynamic-toggle active' data-wallpaper-motion='dynamic' aria-pressed='true'")
expect(html).to_contain("class='wallpaper-swatches' role='radiogroup' aria-label='Wallpaper choices'")
expect(html).to_contain("data-wallpaper-choice='aurora'")
expect(html).to_contain("data-wallpaper-choice='dawn'")
expect(html).to_contain("data-wallpaper-choice='graphite'")
expect(html).to_contain("class='wallpaper-preview' role='img' aria-label='Animated aurora wallpaper preview'")
expect(html).to_contain("class='wallpaper-preview-orbit'")
expect(html).to_contain("@keyframes wm-wallpaper-picker-in")
expect(html).to_contain("@keyframes wm-wallpaper-orbit")
expect(html).to_contain("body[data-motion-mode='reduced'] .wallpaper-picker")
expect(html).to_contain("body[data-motion-mode='off'] .wallpaper-picker")
expect(html).to_contain("class='dock-stack'")
expect(html).to_contain("role='dialog' aria-label='Dock stack Downloads'")
expect(html).to_contain("data-motion-scope='dock-stack'")
expect(html).to_contain("data-stack-source='dock'")
expect(html).to_contain("data-stack-layout='fan-grid'")
expect(html).to_contain("class='dock-stack-mode active' data-stack-mode='fan' aria-pressed='true'")
expect(html).to_contain("class='dock-stack-mode' data-stack-mode='grid' aria-pressed='false'")
expect(html).to_contain("class='dock-stack-items' role='listbox' aria-label='Downloads stack items'")
expect(html).to_contain("data-stack-item='screenshot'")
expect(html).to_contain("data-stack-item='report'")
expect(html).to_contain("data-stack-item='archive'")
expect(html).to_contain("class='dock-stack-anchor' aria-hidden='true'")
expect(html).to_contain("@keyframes wm-dock-stack-in")
expect(html).to_contain("@keyframes wm-dock-stack-fan")
expect(html).to_contain("body[data-motion-mode='reduced'] .dock-stack")
expect(html).to_contain("body[data-motion-mode='off'] .dock-stack")
expect(html).to_contain("class='widget-gallery'")
expect(html).to_contain("role='dialog' aria-label='Widget gallery'")
expect(html).to_contain("data-motion-scope='widget-gallery'")
expect(html).to_contain("data-widget-source='desktop-gallery'")
expect(html).to_contain("class='widget-size-control' role='group' aria-label='Widget size'")
expect(html).to_contain("data-widget-size='small'")
expect(html).to_contain("data-widget-size='medium'")
expect(html).to_contain("data-widget-size='large'")
expect(html).to_contain("class='widget-gallery-grid' role='listbox' aria-label='Available widgets'")
expect(html).to_contain("data-widget-kind='clock'")
expect(html).to_contain("data-widget-kind='weather'")
expect(html).to_contain("data-widget-kind='build'")
expect(html).to_contain("class='widget-add-button' data-widget-action='add'")
expect(html).to_contain("@keyframes wm-widget-gallery-in")
expect(html).to_contain("@keyframes wm-widget-card-in")
expect(html).to_contain("body[data-motion-mode='reduced'] .widget-gallery")
expect(html).to_contain("body[data-motion-mode='off'] .widget-gallery")
```

</details>

#### keeps modern chromed affordances bounded on compact scenes

1. var manager = WindowManager new
2. var registry = UiWindowSurfaceRegistry new
   - Expected: bounded_affordances equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = WindowManager.new()
var registry = UiWindowSurfaceRegistry.new()
val shared = shared_wm_scene_from_window_manager(manager, registry, 240, 180)
val scene = shared_wm_scene_to_chromed_wm_scene(shared, _shared_taskbar(), 1000, "09:41", 1)

var bounded_affordances = 0
for elem in scene.elements:
    if elem.kind == "command_palette" or elem.kind == "desktop_widgets" or elem.kind == "control_center" or elem.kind == "window_overview" or elem.kind == "snap_preview" or elem.kind == "notification_toast" or elem.kind == "notification_center" or elem.kind == "live_activity" or elem.kind == "workspace_switcher" or elem.kind == "shortcut_overlay" or elem.kind == "app_launcher" or elem.kind == "context_menu" or elem.kind == "snap_layouts" or elem.kind == "window_switcher" or elem.kind == "quick_settings" or elem.kind == "hot_corner_zone" or elem.kind == "resize_hud" or elem.kind == "gesture_hints" or elem.kind == "taskbar_preview" or elem.kind == "stage_rail" or elem.kind == "screen_capture_overlay" or elem.kind == "clipboard_history" or elem.kind == "privacy_indicator" or elem.kind == "system_hud" or elem.kind == "wallpaper_picker" or elem.kind == "dock_stack" or elem.kind == "widget_gallery":
        bounded_affordances = bounded_affordances + 1
        expect(elem.x).to_be_greater_than(-1)
        expect(elem.y).to_be_greater_than(-1)
        expect(elem.w).to_be_greater_than(-1)
        expect(elem.h).to_be_greater_than(-1)
        expect(elem.x + elem.w).to_be_less_than(scene.width + 1)
        expect(elem.y + elem.h).to_be_less_than(scene.height + 1)

expect(bounded_affordances).to_equal(30)
```

</details>

#### reports visual quality metrics for rendered OS affordances

1. var manager = WindowManager new
2. var registry = UiWindowSurfaceRegistry new
3. registry bind with kind
   - Expected: report.glass_blur_px equals `24`
   - Expected: report.glass_saturation_pct equals `170`
   - Expected: report.glass_opacity_floor_x100 equals `6`
   - Expected: report.max_command_palette_width_px equals `680`
   - Expected: report.max_control_center_width_px equals `320`
   - Expected: report.max_desktop_widget_width_px equals `260`
   - Expected: report.max_notification_width_px equals `360`
   - Expected: report.max_notification_center_width_px equals `340`
   - Expected: report.max_live_activity_width_px equals `420`
   - Expected: report.max_workspace_switcher_width_px equals `360`
   - Expected: report.max_shortcut_overlay_width_px equals `420`
   - Expected: report.max_app_launcher_width_px equals `520`
   - Expected: report.max_context_menu_width_px equals `280`
   - Expected: report.max_snap_layouts_width_px equals `360`
   - Expected: report.max_window_switcher_width_px equals `460`
   - Expected: report.max_quick_settings_width_px equals `300`
   - Expected: report.max_hot_corner_size_px equals `44`
   - Expected: report.max_resize_hud_width_px equals `240`
   - Expected: report.max_gesture_hint_width_px equals `360`
   - Expected: report.max_taskbar_preview_width_px equals `320`
   - Expected: report.max_stage_rail_width_px equals `88`
   - Expected: report.max_screen_capture_width_px equals `560`
   - Expected: report.max_clipboard_history_width_px equals `360`
   - Expected: report.max_privacy_indicator_width_px equals `300`
   - Expected: report.max_system_hud_width_px equals `280`
   - Expected: report.max_wallpaper_picker_width_px equals `380`
   - Expected: report.max_dock_stack_width_px equals `340`
   - Expected: report.max_widget_gallery_width_px equals `440`
   - Expected: report.min_overview_card_width_px equals `180`
   - Expected: report.min_touch_target_height_px equals `44`
   - Expected: report.layout_safe_area_px equals `16`
   - Expected: report.layout_panel_gap_px equals `12`
   - Expected: report.layout_min_touch_target_px equals `44`
   - Expected: report.reduced_motion_duration_ms equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 86 lines folded for reproduction.
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
expect(report.round_scrollbars)
expect(report.round_icon_converter)
expect(report.titlebar_input_ready)
expect(report.traffic_controls_ready)
expect(report.animated_background_ready)
expect(report.window_interaction_ready)
expect(report.command_palette_ready)
expect(report.theme_accent_controls_ready)
expect(report.focus_depth_ready)
expect(report.lifecycle_animation_ready)
expect(report.taskbar_interaction_ready)
expect(report.dock_magnification_ready)
expect(report.notification_feedback_ready)
expect(report.notification_center_ready)
expect(report.live_activity_ready)
expect(report.workspace_switcher_ready)
expect(report.keyboard_shortcut_overlay_ready)
expect(report.app_launcher_ready)
expect(report.context_menu_ready)
expect(report.snap_layouts_ready)
expect(report.window_switcher_ready)
expect(report.quick_settings_ready)
expect(report.hot_corners_ready)
expect(report.resize_hud_ready)
expect(report.gesture_hints_ready)
expect(report.taskbar_preview_ready)
expect(report.stage_rail_ready)
expect(report.screen_capture_ready)
expect(report.clipboard_history_ready)
expect(report.privacy_indicator_ready)
expect(report.system_hud_ready)
expect(report.wallpaper_picker_ready)
expect(report.dock_stack_ready)
expect(report.widget_gallery_ready)
expect(report.color_checked)
expect(report.contrast_ratio_x100).to_be_greater_than(449)
expect(report.bounded_layout)
expect(report.translucent_surfaces)
expect(report.material_policy_ready)
expect(report.glass_blur_px).to_equal(24)
expect(report.glass_saturation_pct).to_equal(170)
expect(report.glass_opacity_floor_x100).to_equal(6)
expect(report.rounded_surface_count).to_be_greater_than(3)
expect(report.max_command_palette_width_px).to_equal(680)
expect(report.max_control_center_width_px).to_equal(320)
expect(report.max_desktop_widget_width_px).to_equal(260)
expect(report.max_notification_width_px).to_equal(360)
expect(report.max_notification_center_width_px).to_equal(340)
expect(report.max_live_activity_width_px).to_equal(420)
expect(report.max_workspace_switcher_width_px).to_equal(360)
expect(report.max_shortcut_overlay_width_px).to_equal(420)
expect(report.max_app_launcher_width_px).to_equal(520)
expect(report.max_context_menu_width_px).to_equal(280)
expect(report.max_snap_layouts_width_px).to_equal(360)
expect(report.max_window_switcher_width_px).to_equal(460)
expect(report.max_quick_settings_width_px).to_equal(300)
expect(report.max_hot_corner_size_px).to_equal(44)
expect(report.max_resize_hud_width_px).to_equal(240)
expect(report.max_gesture_hint_width_px).to_equal(360)
expect(report.max_taskbar_preview_width_px).to_equal(320)
expect(report.max_stage_rail_width_px).to_equal(88)
expect(report.max_screen_capture_width_px).to_equal(560)
expect(report.max_clipboard_history_width_px).to_equal(360)
expect(report.max_privacy_indicator_width_px).to_equal(300)
expect(report.max_system_hud_width_px).to_equal(280)
expect(report.max_wallpaper_picker_width_px).to_equal(380)
expect(report.max_dock_stack_width_px).to_equal(340)
expect(report.max_widget_gallery_width_px).to_equal(440)
expect(report.min_overview_card_width_px).to_equal(180)
expect(report.min_touch_target_height_px).to_equal(44)
expect(report.layout_policy_ready)
expect(report.layout_safe_area_px).to_equal(16)
expect(report.layout_panel_gap_px).to_equal(12)
expect(report.layout_min_touch_target_px).to_equal(44)
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
<summary>Executable SSpec</summary>

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
<summary>Executable SSpec</summary>

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

#### fails visual quality when duplicate affordances hide a missing affordance kind

1. SceneElement
2. SceneElement
3. SceneElement
4. SceneElement
5. SceneElement
6. expect not
7. expect not
   - Expected: report.reduced_motion_duration_ms equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = WmSceneSpec(
    name: "duplicate_affordance_scene",
    width: 800,
    height: 600,
    elements: [
        SceneElement(kind: "desktop_chrome", x: 0, y: 0, w: 800, h: 600, color: 0xFF101418u32, text: ""),
        SceneElement(kind: "control_center", x: 460, y: 60, w: 260, h: 180, color: 0xDD111827u32, text: "controls"),
        SceneElement(kind: "window_overview", x: 80, y: 90, w: 220, h: 120, color: 0xDD020617u32, text: "overview"),
        SceneElement(kind: "snap_preview", x: 320, y: 80, w: 160, h: 180, color: 0x552563EBu32, text: "left"),
        SceneElement(kind: "snap_preview", x: 500, y: 280, w: 160, h: 180, color: 0x552563EBu32, text: "right")
    ]
)
val report = wm_scene_visual_quality_report(scene)

expect_not(report.passed)
expect_not(report.motion_can_disable)
expect(report.reduced_motion_duration_ms).to_equal(0)
```

</details>

#### reports true max widths and actual overview width for malformed affordances

1. SceneElement
2. SceneElement
3. SceneElement
4. SceneElement
5. SceneElement
6. SceneElement
7. SceneElement
8. expect not
9. expect not
   - Expected: report.max_control_center_width_px equals `340`
   - Expected: report.max_desktop_widget_width_px equals `280`
   - Expected: report.min_overview_card_width_px equals `120`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = WmSceneSpec(
    name: "malformed_affordance_scene",
    width: 900,
    height: 640,
    elements: [
        SceneElement(kind: "desktop_chrome", x: 0, y: 0, w: 900, h: 640, color: 0xFF101418u32, text: ""),
        SceneElement(kind: "control_center", x: 520, y: 60, w: 280, h: 180, color: 0xDD111827u32, text: "controls"),
        SceneElement(kind: "control_center", x: 520, y: 260, w: 340, h: 180, color: 0xDD111827u32, text: "wide controls"),
        SceneElement(kind: "desktop_widgets", x: 40, y: 70, w: 220, h: 140, color: 0xCC111827u32, text: "widgets"),
        SceneElement(kind: "desktop_widgets", x: 40, y: 230, w: 280, h: 140, color: 0xCC111827u32, text: "wide widgets"),
        SceneElement(kind: "window_overview", x: 340, y: 120, w: 120, h: 120, color: 0xDD020617u32, text: "narrow overview"),
        SceneElement(kind: "snap_preview", x: 620, y: 60, w: 160, h: 180, color: 0x552563EBu32, text: "right")
    ]
)
val report = wm_scene_visual_quality_report(scene)

expect_not(report.passed)
expect_not(report.bounded_layout)
expect(report.max_control_center_width_px).to_equal(340)
expect(report.max_desktop_widget_width_px).to_equal(280)
expect(report.min_overview_card_width_px).to_equal(120)
```

</details>

#### fails visual quality when titlebar command chrome is missing

1. SceneElement
2. SceneElement
3. SceneElement
4. SceneElement
5. SceneElement
6. expect not
7. expect not
8. expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = WmSceneSpec(
    name: "missing_titlebar_chrome_scene",
    width: 900,
    height: 640,
    elements: [
        SceneElement(kind: "desktop_chrome", x: 0, y: 0, w: 900, h: 640, color: 0xFF101418u32, text: ""),
        SceneElement(kind: "control_center", x: 520, y: 60, w: 280, h: 180, color: 0xDD111827u32, text: "controls"),
        SceneElement(kind: "desktop_widgets", x: 40, y: 70, w: 220, h: 140, color: 0xCC111827u32, text: "widgets"),
        SceneElement(kind: "window_overview", x: 340, y: 120, w: 220, h: 120, color: 0xDD020617u32, text: "overview"),
        SceneElement(kind: "snap_preview", x: 620, y: 60, w: 160, h: 180, color: 0x552563EBu32, text: "right")
    ]
)
val report = wm_scene_visual_quality_report(scene)

expect_not(report.passed)
expect_not(report.titlebar_input_ready)
expect_not(report.traffic_controls_ready)
```

</details>

### WmScene — lifecycle motion projection

#### projects host-neutral lifecycle motion classes into inspectable HTML

1. WmLifecycleWindowState
2. WmLifecycleWindowState
   - Expected: opening_scene.name equals `lifecycle_motion_wm_scene`
3. expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
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
expect(opening_html).to_contain("@keyframes wm-window-open")
expect(opening_html).to_contain("@keyframes wm-window-close")
expect(opening_html).to_contain("@keyframes wm-window-minimize")
expect(opening_html).to_contain("@keyframes wm-window-restore")
expect(opening_html).to_contain(".wm-window-opening{{animation:wm-window-open 240ms")
expect(opening_html).to_contain("body[data-motion-mode='reduced'] .motion-window")
expect(opening_html).to_contain("body[data-motion-mode='off'] .motion-window")
expect_not(opening_html.contains("Hidden"))

val minimizing_scene = lifecycle_windows_to_motion_wm_scene(windows, "minimize", 640, 480)
val minimizing_html = scene_to_html(minimizing_scene)
expect(minimizing_html).to_contain("wm-window-minimizing")
expect(minimizing_html).to_contain(".wm-window-minimizing{{animation:wm-window-minimize 180ms")
expect(minimizing_html).to_contain("data-title='Hidden'")
expect(minimizing_html).to_contain("data-motion-duration-ms='180'")
expect(minimizing_html).to_contain("data-motion-easing='cubic-bezier(.4,0,.2,1)'")
expect(minimizing_html).to_contain("data-motion-transform-origin='dock'")
expect(minimizing_html).to_contain("data-dock-origin-x='150'")
expect(minimizing_html).to_contain("data-dock-origin-y='288'")
expect(minimizing_html).to_contain("--dock-origin-x:150px")
expect(minimizing_html).to_contain("--dock-origin-y:288px")
expect(minimizing_html).to_contain(".motion-window[data-motion-transform-origin='dock']")

val restoring_scene = lifecycle_windows_to_motion_wm_scene(windows, "restore", 640, 480)
val restoring_html = scene_to_html(restoring_scene)
expect(restoring_html).to_contain("wm-window-restoring")
expect(restoring_html).to_contain(".wm-window-restoring{{animation:wm-window-restore 240ms")
expect(restoring_html).to_contain("data-motion-phase='restoring'")
expect(restoring_html).to_contain("data-motion-easing='cubic-bezier(.2,.8,.2,1)'")
expect(restoring_html).to_contain("data-motion-transform-origin='dock'")
expect(restoring_html).to_contain("data-dock-origin-x='150'")
expect(restoring_html).to_contain("data-dock-origin-y='288'")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/wm_scene_spec.spl` |
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
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
