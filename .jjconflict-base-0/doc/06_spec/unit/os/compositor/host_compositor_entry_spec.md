# Host Compositor Entry Spec

Deterministic unit tests for the shared host compositor bootstrap boundary.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/host_compositor_entry_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Deterministic unit tests for the shared host compositor bootstrap boundary.
Tests avoid creating real host windows except for the TUI nil boundary, which
returns before touching SFFI.

## Scenarios

### HostBackendKind variants

#### includes platform-native backend variants

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdl = HostBackendKind.Sdl2
val cocoa = HostBackendKind.Cocoa
val win32 = HostBackendKind.Win32
val headless = HostBackendKind.Headless
expect(sdl != cocoa).to_equal(true)
expect(win32 != headless).to_equal(true)
```

</details>

#### Headless backend creates a usable handle via init_host_wm

1. initial size: Size wh
   - Expected: handle != nil is true
   - Expected: handle.compositor.width equals `640`
   - Expected: handle.compositor.height equals `480`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = HostWmConfig(
    backend: HostBackendKind.Headless,
    initial_size: Size.wh(640, 480),
    title: "headless-wm"
)
val handle = init_host_wm(cfg)
expect(handle != nil).to_equal(true)
expect(handle.compositor.width).to_equal(640)
expect(handle.compositor.height).to_equal(480)
```

</details>

### HostWmConfig

#### keeps title in the bootstrap contract

1. initial size: Size wh
   - Expected: cfg.title equals `electron-test`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = HostWmConfig(
    backend: HostBackendKind.Electron,
    initial_size: Size.wh(1280, 800),
    title: "electron-test"
)
expect(cfg.title).to_equal("electron-test")
```

</details>

#### can name Tauri as a host WM shell adapter

1. initial size: Size wh
   - Expected: cfg.backend == HostBackendKind.Tauri is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = HostWmConfig(
    backend: HostBackendKind.Tauri,
    initial_size: Size.wh(1280, 800),
    title: "tauri-test"
)
expect(cfg.backend == HostBackendKind.Tauri).to_equal(true)
```

</details>

### host surface failure boundaries

<details>
<summary>Advanced: accepts a nonzero event loop and window surface</summary>

#### accepts a nonzero event loop and window surface

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = host_wm_surface_failure_reason(_browser_config(), 10, 20)
expect(reason == nil).to_equal(true)
```

</details>


</details>

#### accepts Tauri at the host surface contract boundary

1. initial size: Size wh
   - Expected: reason == nil is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = HostWmConfig(
    backend: HostBackendKind.Tauri,
    initial_size: Size.wh(1280, 800),
    title: "tauri-wm"
)
val reason = host_wm_surface_failure_reason(cfg, 10, 20)
expect(reason == nil).to_equal(true)
```

</details>

#### documents the TUI stub boundary

1. initial size: Size wh
   - Expected: reason equals `tui host compositor bootstrap is not implemented`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = HostWmConfig(
    backend: HostBackendKind.Tui,
    initial_size: Size.wh(80, 24),
    title: "tui-wm"
)
val reason = host_wm_surface_failure_reason(cfg, 10, 20)
expect(reason).to_equal("tui host compositor bootstrap is not implemented")
```

</details>

#### rejects zero-sized host surfaces before SFFI bootstrap

1. initial size: Size wh
   - Expected: reason equals `host compositor size must be nonzero`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = HostWmConfig(
    backend: HostBackendKind.Browser,
    initial_size: Size.wh(0, 240),
    title: "bad-size"
)
val reason = host_wm_surface_failure_reason(cfg, 10, 20)
expect(reason).to_equal("host compositor size must be nonzero")
```

</details>

#### returns nil for TUI without touching host window SFFI

1. initial size: Size wh
   - Expected: result == nil is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = HostWmConfig(
    backend: HostBackendKind.Tui,
    initial_size: Size.wh(80, 24),
    title: "tui-wm"
)
val result = init_host_wm(cfg)
expect(result == nil).to_equal(true)
```

</details>

### host WM bootstrap

#### creates a Browser host WM handle on the shared compositor path

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = init_host_wm(_browser_config())
expect(handle != nil).to_equal(true)
expect(handle.event_loop_id).to_equal(1)
expect(handle.window_id).to_equal(1)
expect(handle.compositor.width).to_equal(320)
expect(handle.compositor.height).to_equal(240)
```

</details>

#### creates an Electron host WM handle on the shared compositor path

1. initial size: Size wh
   - Expected: handle != nil is true
   - Expected: handle.compositor.width equals `800`
   - Expected: handle.compositor.height equals `600`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = HostWmConfig(
    backend: HostBackendKind.Electron,
    initial_size: Size.wh(800, 600),
    title: "electron-wm"
)
val handle = init_host_wm(cfg)
expect(handle != nil).to_equal(true)
expect(handle.compositor.width).to_equal(800)
expect(handle.compositor.height).to_equal(600)
```

</details>

#### creates a Tauri host WM handle on the shared compositor path

1. initial size: Size wh
   - Expected: handle != nil is true
   - Expected: handle.compositor.width equals `1024`
   - Expected: handle.compositor.height equals `768`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = HostWmConfig(
    backend: HostBackendKind.Tauri,
    initial_size: Size.wh(1024, 768),
    title: "tauri-wm"
)
val handle = init_host_wm(cfg)
expect(handle != nil).to_equal(true)
expect(handle.compositor.width).to_equal(1024)
expect(handle.compositor.height).to_equal(768)
```

</details>

### HostWmHandle loop behavior

<details>
<summary>Advanced: runs one tick without host event polling when no event loop is attached</summary>

#### runs one tick without host event polling when no event loop is attached

1. var comp = HostCompositor new

2. wm:  running wm service

3. handle run once
   - Expected: pumped equals `0`
   - Expected: _fake_present_count equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_fake_present_count = 0
val backend = FakeCompositorBackend(w: 320, h: 240)
var comp = HostCompositor.new(backend, Size.wh(320, 240))
val handle = HostWmHandle(
    compositor: comp,
    wm: _running_wm_service(),
    event_loop_id: 0,
    window_id: 0,
    backend: HostBackendKind.Browser
)
val pumped = handle.pump_host_events()
handle.run_once()
expect(pumped).to_equal(0)
expect(_fake_present_count).to_equal(1)
```

</details>


</details>

#### renders hosted windows through the Simple Web app content path

1. comp apply bridge request

2. comp render frame
   - Expected: _capture_present_count equals `1`
   - Expected: _capture_clear_color equals `0xFF0F172Au32`


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_capture_present_count = 0
_capture_blue_count = 0
_capture_white_count = 0
_capture_engine_title_count = 0
_capture_engine_content_count = 0
_capture_blit_count = 0
_capture_clear_color = 0u32
val backend = CaptureCompositorBackend.with_color(80, 70, 0xFF000000u32)
val comp = HostCompositor.new(backend, Size.wh(80, 70))
comp.apply_bridge_request(1, 77, COMP_CREATE_WINDOW.to_i64(), 0, "Terminal", 8, 8, 40, 52, "ready", 900, "/sys/apps/terminal")
comp.render_frame()
expect(_capture_present_count).to_equal(1)
expect(_capture_blue_count).to_be_greater_than(0)
expect(_capture_white_count).to_be_greater_than(0)
expect(_capture_blit_count).to_be_greater_than(0)
expect(_capture_clear_color).to_equal(0xFF0F172Au32)
```

</details>

#### records compositor resize dimensions

1. comp resize
   - Expected: comp.width equals `640`
   - Expected: comp.height equals `480`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = FakeCompositorBackend(w: 320, h: 240)
val comp = HostCompositor.new(backend, Size.wh(320, 240))
comp.resize(640, 480)
expect(comp.width).to_equal(640)
expect(comp.height).to_equal(480)
```

</details>

#### does not tick after the WM has stopped

1. handle run once
   - Expected: _fake_present_count equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_fake_present_count = 0
val backend = FakeCompositorBackend(w: 320, h: 240)
val comp = HostCompositor.new(backend, Size.wh(320, 240))
val wm = WmService.new()
val handle = HostWmHandle(
    compositor: comp,
    wm: wm,
    event_loop_id: 0,
    window_id: 0,
    backend: HostBackendKind.Browser
)
handle.run_once()
expect(_fake_present_count).to_equal(0)
```

</details>

#### returns immediately from tick_forever when the WM is already stopped

1. handle tick forever
   - Expected: _fake_present_count equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_fake_present_count = 0
val backend = FakeCompositorBackend(w: 320, h: 240)
val comp = HostCompositor.new(backend, Size.wh(320, 240))
val wm = WmService.new()
val handle = HostWmHandle(
    compositor: comp,
    wm: wm,
    event_loop_id: 1,
    window_id: 1,
    backend: HostBackendKind.Browser
)
handle.tick_forever()
expect(_fake_present_count).to_equal(0)
```

</details>

#### uses a nonzero idle sleep interval for tick_forever

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(HOST_WM_IDLE_SLEEP_MS).to_be_greater_than(0)
```

</details>

#### keeps Browser Electron and Tauri on the shared Simple Web content renderer

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val browser = init_host_wm(HostWmConfig(backend: HostBackendKind.Browser, initial_size: Size.wh(320, 240), title: "browser-wm"))
val electron = init_host_wm(HostWmConfig(backend: HostBackendKind.Electron, initial_size: Size.wh(320, 240), title: "electron-wm"))
val tauri = init_host_wm(HostWmConfig(backend: HostBackendKind.Tauri, initial_size: Size.wh(320, 240), title: "tauri-wm"))

expect(browser != nil).to_equal(true)
expect(electron != nil).to_equal(true)
expect(tauri != nil).to_equal(true)
expect(host_wm_content_renderer_name(browser)).to_equal(WEB_RENDER_TARGET_SIMPLE_WEB)
expect(host_wm_content_renderer_name(electron)).to_equal(WEB_RENDER_TARGET_SIMPLE_WEB)
expect(host_wm_content_renderer_name(tauri)).to_equal(WEB_RENDER_TARGET_SIMPLE_WEB)
```

</details>

### HostCompositor hosted window state

#### creates, updates, minimizes, restores, and destroys hosted windows

1. comp apply bridge request
   - Expected: comp.windows.len() equals `1`
   - Expected: comp.windows[0].title equals `Hosted App`
   - Expected: comp.windows[0].focused is true

2. comp apply bridge request
   - Expected: comp.windows[0].content equals `rendered content`

3. comp apply bridge request
   - Expected: comp.windows[0].minimized is true

4. comp apply bridge request
   - Expected: comp.windows[0].minimized is false
   - Expected: comp.windows[0].focused is true

5. comp apply bridge request
   - Expected: comp.windows.len() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = FakeCompositorBackend(w: 640, h: 480)
val comp = HostCompositor.new(backend, Size.wh(640, 480))
comp.apply_bridge_request(1, 77, COMP_CREATE_WINDOW.to_i64(), 0, "Hosted App", 40, 50, 320, 180, "", 900, "/sys/apps/test")
expect(comp.windows.len()).to_equal(1)
expect(comp.windows[0].title).to_equal("Hosted App")
expect(comp.windows[0].focused).to_equal(true)

val wid = comp.windows[0].id
comp.apply_bridge_request(2, 77, COMP_UPDATE_TREE.to_i64(), wid, "", 0, 0, 0, 0, "rendered content", 0, "/sys/apps/test")
expect(comp.windows[0].content).to_equal("rendered content")

comp.apply_bridge_request(3, 77, COMP_MINIMIZE.to_i64(), wid, "", 0, 0, 0, 0, "", 0, "/sys/apps/test")
expect(comp.windows[0].minimized).to_equal(true)

comp.apply_bridge_request(4, 77, COMP_RESTORE.to_i64(), wid, "", 0, 0, 0, 0, "", 0, "/sys/apps/test")
expect(comp.windows[0].minimized).to_equal(false)
expect(comp.windows[0].focused).to_equal(true)

comp.apply_bridge_request(5, 77, COMP_DESTROY_WINDOW.to_i64(), wid, "", 0, 0, 0, 0, "", 0, "/sys/apps/test")
expect(comp.windows.len()).to_equal(0)
```

</details>

#### applies host bridge lifecycle requests through shared WM actions

1. comp apply bridge request

2. comp apply bridge request

3. comp apply bridge request

4. comp apply bridge request

5. comp apply bridge request
   - Expected: comp.windows[0].x equals `120`
   - Expected: comp.windows[0].y equals `130`
   - Expected: comp.windows[0].w equals `320`
   - Expected: comp.windows[0].h equals `220`
   - Expected: comp.windows[0].title equals `One Renamed`

6. comp apply bridge request
   - Expected: comp.windows[comp.windows.len() - 1].id equals `first_id`

7. comp apply bridge request
   - Expected: comp.windows[comp.windows.len() - 1].x equals `0`
   - Expected: comp.windows[comp.windows.len() - 1].y equals `48`
   - Expected: comp.windows[comp.windows.len() - 1].w equals `640`
   - Expected: comp.windows[comp.windows.len() - 1].h equals `384`


<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = FakeCompositorBackend(w: 640, h: 480)
val comp = HostCompositor.new(backend, Size.wh(640, 480))
comp.apply_bridge_request(1, 77, COMP_CREATE_WINDOW.to_i64(), 0, "One", 40, 50, 240, 160, "", 1, "/sys/apps/one")
comp.apply_bridge_request(2, 88, COMP_CREATE_WINDOW.to_i64(), 0, "Two", 80, 90, 240, 160, "", 2, "/sys/apps/two")

val first_id = comp.windows[0].id
comp.apply_bridge_request(3, 77, COMP_MOVE.to_i64(), first_id, "", 120, 130, 0, 0, "", 0, "")
comp.apply_bridge_request(4, 77, COMP_RESIZE.to_i64(), first_id, "", 0, 0, 320, 220, "", 0, "")
comp.apply_bridge_request(5, 77, COMP_SET_TITLE.to_i64(), first_id, "One Renamed", 0, 0, 0, 0, "", 0, "")
expect(comp.windows[0].x).to_equal(120)
expect(comp.windows[0].y).to_equal(130)
expect(comp.windows[0].w).to_equal(320)
expect(comp.windows[0].h).to_equal(220)
expect(comp.windows[0].title).to_equal("One Renamed")

comp.apply_bridge_request(6, 77, COMP_FOCUS.to_i64(), first_id, "", 0, 0, 0, 0, "", 0, "")
expect(comp.windows[comp.windows.len() - 1].id).to_equal(first_id)
comp.apply_bridge_request(7, 77, COMP_MAXIMIZE.to_i64(), first_id, "", 0, 0, 0, 0, "", 0, "")
expect(comp.windows[comp.windows.len() - 1].x).to_equal(0)
expect(comp.windows[comp.windows.len() - 1].y).to_equal(48)
expect(comp.windows[comp.windows.len() - 1].w).to_equal(640)
expect(comp.windows[comp.windows.len() - 1].h).to_equal(384)
```

</details>

#### maps taskbar hit to the expected window and restores focus

1. comp apply bridge request

2. comp apply bridge request
   - Expected: comp.hit_taskbar(first_x + 20, dock_y + 16) equals `first_id`

3. comp apply bridge request

4. comp focus window
   - Expected: comp.windows[comp.windows.len() - 1].id equals `first_id`
   - Expected: comp.windows[comp.windows.len() - 1].minimized is false

5. comp destroy window
   - Expected: comp.windows.len() equals `1`
   - Expected: comp.windows[0].id == first_id is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = FakeCompositorBackend(w: 640, h: 480)
val comp = HostCompositor.new(backend, Size.wh(640, 480))
comp.apply_bridge_request(1, 11, COMP_CREATE_WINDOW.to_i64(), 0, "One", 20, 60, 200, 140, "", 1, "/sys/apps/one")
comp.apply_bridge_request(2, 22, COMP_CREATE_WINDOW.to_i64(), 0, "Two", 50, 90, 200, 140, "", 2, "/sys/apps/two")
val first_id = comp.windows[0].id
val dock_y = 480 - 62
val first_x = host_taskbar_item_x(640, comp.windows.len(), 0)
expect(comp.hit_taskbar(first_x + 20, dock_y + 16)).to_equal(first_id)
comp.apply_bridge_request(3, 11, COMP_MINIMIZE.to_i64(), first_id, "", 0, 0, 0, 0, "", 0, "/sys/apps/one")
comp.focus_window(first_id)
expect(comp.windows[comp.windows.len() - 1].id).to_equal(first_id)
expect(comp.windows[comp.windows.len() - 1].minimized).to_equal(false)
comp.destroy_window(first_id)
expect(comp.windows.len()).to_equal(1)
expect(comp.windows[0].id == first_id).to_equal(false)
```

</details>

#### keeps overflow taskbar entries clickable past four windows

1. comp apply bridge request

2. comp apply bridge request

3. comp apply bridge request

4. comp apply bridge request

5. comp apply bridge request

6. comp apply bridge request
   - Expected: comp.hit_taskbar(last_x + (item_w / 2), dock_y + 16) equals `comp.windows[5].id`


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = FakeCompositorBackend(w: 640, h: 480)
val comp = HostCompositor.new(backend, Size.wh(640, 480))
comp.apply_bridge_request(1, 11, COMP_CREATE_WINDOW.to_i64(), 0, "App 0", 20, 60, 200, 140, "", 1, "/sys/apps/app0")
comp.apply_bridge_request(2, 12, COMP_CREATE_WINDOW.to_i64(), 0, "App 1", 30, 68, 200, 140, "", 2, "/sys/apps/app1")
comp.apply_bridge_request(3, 13, COMP_CREATE_WINDOW.to_i64(), 0, "App 2", 40, 76, 200, 140, "", 3, "/sys/apps/app2")
comp.apply_bridge_request(4, 14, COMP_CREATE_WINDOW.to_i64(), 0, "App 3", 50, 84, 200, 140, "", 4, "/sys/apps/app3")
comp.apply_bridge_request(5, 15, COMP_CREATE_WINDOW.to_i64(), 0, "App 4", 60, 92, 200, 140, "", 5, "/sys/apps/app4")
comp.apply_bridge_request(6, 16, COMP_CREATE_WINDOW.to_i64(), 0, "App 5", 70, 100, 200, 140, "", 6, "/sys/apps/app5")
val count = comp.windows.len()
val dock_w = host_taskbar_dock_width(640, count)
val item_w = host_taskbar_item_width(640, count)
val last_x = host_taskbar_item_x(640, count, 5)
val dock_y = 480 - 62
expect(dock_w).to_be_less_than(640)
expect(comp.hit_taskbar(last_x + (item_w / 2), dock_y + 16)).to_equal(comp.windows[5].id)
```

</details>

#### clamps dragged windows inside the visible desktop

1. comp apply bridge request

2. comp = host compositor pointer move
   - Expected: comp.windows[0].x equals `0`
   - Expected: comp.windows[0].y equals `48`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = FakeCompositorBackend(w: 320, h: 240)
val comp = HostCompositor.new(backend, Size.wh(320, 240))
comp.apply_bridge_request(1, 77, COMP_CREATE_WINDOW.to_i64(), 0, "Drag", 40, 70, 120, 90, "", 1, "/sys/apps/drag")
val wid = comp.windows[0].id
comp.dragging = true
comp.drag_window_id = wid
comp.drag_offset_x = 60
comp.drag_offset_y = 40
comp = host_compositor_pointer_move(comp, -20, 10)
expect(comp.windows[0].x).to_equal(0)
expect(comp.windows[0].y).to_equal(48)
```

</details>

#### resizes windows from the visible bottom-right grip

1. var comp = HostCompositor new

2. comp apply bridge request

3. comp = host compositor pointer move

4. comp = host compositor left button
   - Expected: comp.resizing is true

5. comp = host compositor pointer move
   - Expected: comp.windows[0].w equals `242`
   - Expected: comp.windows[0].h equals `192`

6. comp = host compositor left button
   - Expected: comp.resizing is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = FakeCompositorBackend(w: 640, h: 480)
var comp = HostCompositor.new(backend, Size.wh(640, 480))
comp.apply_bridge_request(1, 77, COMP_CREATE_WINDOW.to_i64(), 0, "Resize", 40, 70, 200, 160, "", 1, "/sys/apps/resize")
comp = host_compositor_pointer_move(comp, 238, 228)
comp = host_compositor_left_button(comp, true)
expect(comp.resizing).to_equal(true)
comp = host_compositor_pointer_move(comp, 280, 260)
expect(comp.windows[0].w).to_equal(242)
expect(comp.windows[0].h).to_equal(192)
comp = host_compositor_left_button(comp, false)
expect(comp.resizing).to_equal(false)
```

</details>

#### routes host-native mouse resize through the shared input helper

1. comp apply bridge request

2. comp handle mouse move

3. comp handle left button
   - Expected: comp.resizing is true

4. comp handle mouse move
   - Expected: comp.windows[0].w equals `242`
   - Expected: comp.windows[0].h equals `192`

5. comp handle left button
   - Expected: comp.resizing is false
   - Expected: comp.resize_window_id equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = FakeCompositorBackend(w: 640, h: 480)
val comp = HostCompositor.new(backend, Size.wh(640, 480))
comp.apply_bridge_request(1, 77, COMP_CREATE_WINDOW.to_i64(), 0, "Host Native Resize", 40, 70, 200, 160, "", 1, "/sys/apps/resize")
comp.handle_mouse_move(238, 228)
comp.handle_left_button(true)
expect(comp.resizing).to_equal(true)
comp.handle_mouse_move(280, 260)
expect(comp.windows[0].w).to_equal(242)
expect(comp.windows[0].h).to_equal(192)
comp.handle_left_button(false)
expect(comp.resizing).to_equal(false)
expect(comp.resize_window_id).to_equal(0)
```

</details>

#### clamps user resize to the hosted WM minimum size

1. var comp = HostCompositor new

2. comp apply bridge request

3. comp = host compositor pointer move

4. comp = host compositor left button

5. comp = host compositor pointer move
   - Expected: comp.windows[0].w equals `160`
   - Expected: comp.windows[0].h equals `120`

6. comp = host compositor left button


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = FakeCompositorBackend(w: 640, h: 480)
var comp = HostCompositor.new(backend, Size.wh(640, 480))
comp.apply_bridge_request(1, 77, COMP_CREATE_WINDOW.to_i64(), 0, "Resize Min", 40, 70, 200, 160, "", 1, "/sys/apps/resize")
comp = host_compositor_pointer_move(comp, 238, 228)
comp = host_compositor_left_button(comp, true)
comp = host_compositor_pointer_move(comp, 0, 0)
expect(comp.windows[0].w).to_equal(160)
expect(comp.windows[0].h).to_equal(120)
comp = host_compositor_left_button(comp, false)
```

</details>

#### records a visible failure window for a child that exits before creating a window

1. comp record launch failure
   - Expected: comp.app_processes[0].failed is true
   - Expected: comp.windows.len() equals `1`
   - Expected: comp.windows[0].title equals `Broken failed`


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = FakeCompositorBackend(w: 640, h: 480)
val comp = HostCompositor.new(backend, Size.wh(640, 480))
comp.app_processes.push(HostWmAppProcess(
    title: "Broken",
    app_id: "/sys/apps/broken",
    source_path: "src/app/hosted_apps/broken.spl",
    pid: -1,
    failed: false
))
comp.record_launch_failure(0)
expect(comp.app_processes[0].failed).to_equal(true)
expect(comp.windows.len()).to_equal(1)
expect(comp.windows[0].title).to_equal("Broken failed")
expect(comp.windows[0].content).to_contain("failed to create a window")
```

</details>

### SimpleOS GUI adapter proof

#### delivers display app events and input through the shared WM path

1. adapter deliver bridge request

2. adapter deliver pointer move

3. adapter deliver left button

4. adapter deliver pointer move

5. adapter deliver left button

6. adapter render framebuffer frame
   - Expected: simpleos_gui_adapter_display_path_name(adapter) equals `simpleos-framebuffer`
   - Expected: simpleos_gui_adapter_content_renderer_name(adapter) equals `WEB_RENDER_TARGET_SIMPLE_WEB`
   - Expected: adapter.delivered_bridge_events equals `1`
   - Expected: adapter.delivered_input_events equals `4`
   - Expected: adapter.presented_frames equals `1`
   - Expected: adapter.compositor.windows[0].id equals `window_id`
   - Expected: _capture_present_count equals `1`
   - Expected: _capture_clear_color equals `0xFF0F172Au32`


<details>
<summary>Executable SPipe</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_capture_present_count = 0
_capture_blue_count = 0
_capture_engine_title_count = 0
_capture_engine_content_count = 0
_capture_blit_count = 0
_capture_clear_color = 0u32
val backend = CaptureCompositorBackend.with_color(200, 150, 0xFF000000u32)
val adapter = SimpleOsGuiAdapter.new(backend, Size.wh(200, 150))

adapter.deliver_bridge_request(1, 44, COMP_CREATE_WINDOW.to_i64(), 0, "Terminal", 20, 30, 128, 92, "adapter-ready", 800, "/sys/apps/terminal")
val window_id = adapter.compositor.windows[0].id
adapter.deliver_pointer_move(146, 120)
adapter.deliver_left_button(true)
adapter.deliver_pointer_move(180, 145)
adapter.deliver_left_button(false)
adapter.render_framebuffer_frame()

expect(simpleos_gui_adapter_display_path_name(adapter)).to_equal("simpleos-framebuffer")
expect(simpleos_gui_adapter_content_renderer_name(adapter)).to_equal(WEB_RENDER_TARGET_SIMPLE_WEB)
expect(adapter.delivered_bridge_events).to_equal(1)
expect(adapter.delivered_input_events).to_equal(4)
expect(adapter.presented_frames).to_equal(1)
expect(adapter.compositor.windows[0].id).to_equal(window_id)
expect(adapter.compositor.windows[0].w).to_be_greater_than(128)
expect(adapter.compositor.windows[0].h).to_be_greater_than(92)
expect(_capture_present_count).to_equal(1)
expect(_capture_blue_count).to_be_greater_than(0)
expect(_capture_clear_color).to_equal(0xFF0F172Au32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

