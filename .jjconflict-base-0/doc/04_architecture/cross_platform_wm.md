# Cross-Platform Window Manager — Architecture

> **Scope note.** This doc covers the full GUI drawing stack — not just
> baremetal SimpleOS. All compositor backends (Fb, GPU, Hosted,
> Browser/SimpleWeb, Electron) share the same headless WM service,
> `Compositor` + `InputBackend` traits, widget/session layer, and Simple
> 2D rendering model. For the work plan that maps the drawing stack
> variations onto these modules, see
> [`doc/03_plan/gui_drawing_layer_variations.md`](../03_plan/gui_drawing_layer_variations.md).
> For the dev-facing "which backend do I pick" guide, see
> [`doc/07_guide/ui_stack_guide.md`](../07_guide/ui_stack_guide.md).

## Current State

```
┌─────────────────────────────────────────────────────────┐
│                    DesktopShell                          │
│  (taskbar, app launcher, shortcuts, WM service)         │
├─────────────────────────────────────────────────────────┤
│                    Compositor                            │
│  (Z-order surfaces, input routing, drag, focus)         │
│  Uses: FramebufferDriver directly (hardcoded)           │
├──────────┬──────────┬───────────────────────────────────┤
│ Ps2Keyboard │ Ps2Mouse │ decorations, cursor, layout   │
├──────────┴──────────┴───────────────────────────────────┤
│              CompositorBackend (trait)                   │
│  ┌──────────────────┐  ┌────────────────────┐           │
│  │ FbCompositorBackend│  │GpuCompositorBackend│          │
│  │ (FramebufferDriver)│  │(VirtioGpuDriver)  │          │
│  └──────────────────┘  └────────────────────┘           │
└─────────────────────────────────────────────────────────┘

Separate (not integrated):
  examples/simple_os/hosted/ — standalone pixel rendering via winit
  (duplicates rendering logic, doesn't use CompositorBackend)
```

**Problems:**
1. `Compositor` hardcodes `FramebufferDriver` + `Ps2Keyboard` + `Ps2Mouse`
2. Hosted desktop duplicates rendering logic
3. No shared input abstraction between PS/2 and winit

> **Status note (2026-04-14).** Problems 1–3 have been resolved. The
> `CompositorBackend` / `InputBackend` traits and their Fb / GPU /
> Hosted / Browser / Electron implementations all live under
> `src/os/compositor/` (see File Layout below). This section is kept
> for historical context only.

## Target Architecture

```
┌──────────────────────────────────────────────────────────────────┐
│                          Application                             │
│   os.apps.* · examples/* — imports only common.ui.* (GUI Lib)    │
├──────────────────────────────────────────────────────────────────┤
│                          GUI Lib                                  │
│   common.ui.widget · builder · session (UISession) · layout ·    │
│   diff · changelog · lifecycle · surface · profile · capability  │
│   — single entry for CLI, TUI, and GUI backends                  │
├──────────────────────────────────────────────────────────────────┤
│                   Window Manager Service                          │
│   headless service: session, window, taskbar, focus, lifecycle   │
│   os.services.wm · lib.nogc_sync_mut.play.wm · window_protocol   │
├──────────────────────────────────────────────────────────────────┤
│                          Compositor                               │
│   (Z-order, input routing, drag, focus, decorations, cursor)     │
│   Uses: CompositorBackend + InputBackend (traits)                │
├──────────────────────────────────────────────────────────────────┤
│  InputBackend (trait)           CompositorBackend (trait)        │
│  ┌──────────┬───────────┐      ┌─────┬─────┬──────┬─────┬─────┐ │
│  │Ps2Input  │HostedInput│      │ Fb  │ GPU │Hosted│Brwsr│Elec.│ │
│  │(baremet.)│(winit)    │      │Back.│Back.│Back. │Back.│Back.│ │
│  ├──────────┴───────────┤      └─────┴─────┴──────┴─────┴─────┘ │
│  │BrowserInput│ElectronInput│                                    │
│  │(DOM events)│(ipc events) │                                    │
│  └──────────┴───────────┘                                        │
├──────────────────────────────────────────────────────────────────┤
│                        2D Engine                                  │
│   lib.common.render_scene · lib.gc_async_mut.gpu.engine2d        │
│   backends: cpu · software · vulkan · metal · opengl · virtio_   │
│             gpu · cuda · rocm · intel · baremetal               │
├──────────────────────────────────────────────────────────────────┤
│                       Platform Layer                              │
│  SimpleOS  : PS/2 ports, MMIO framebuffer, VirtIO-GPU, SimpleWeb │
│  Host OS   : winit/Cocoa/Win32/WebCanvas on macOS/Linux/Windows  │
│  SimpleWeb : HTMLCanvas/WebGPU through the shared Simple 2D engine│
│  Electron  : BrowserWindow via main+renderer IPC                 │
└──────────────────────────────────────────────────────────────────┘
```

## Runtime Environments

The WM is always split into two parts:

1. **Headless WM service.** Owns session state, windows, z-order, focus,
   taskbar state, lifecycle, input routing, and protocol state. This service is
   the authority in host mode and SimpleOS mode.
2. **GUI frontend.** Renders the service state and forwards input through the
   selected backend. Frontends may be native, web-hosted, Electron-hosted, or
   SimpleOS-backed, but they do not own WM state.

### Host mode

Host mode runs on macOS, Linux, Windows, and the other supported hosted
platforms. It has two web-capable frontend families:

- **Electron GUI backend**: Electron/BrowserWindow host adapter. It uses the
  `ui.web` protocol plus native host-window commands.
- **Simple web backend**: Chromium-class/simple-browser path. It uses the same
  `ui.web` protocol and renders through the shared Simple 2D engine, not a
  separate browser-only drawing stack.

Host mode supports three presentation modes:

| Mode | Host window shape | Taskbar behavior | WM ownership |
|------|-------------------|------------------|--------------|
| Embedded | One host-native window embeds the full Simple desktop | Simple taskbar visible inside the app window | Simple WM owns app windows and taskbar state |
| Native | Each Simple app maps to its own host-native window | Host OS taskbar/window list shows app windows | Simple WM owns logical state; host owns native shells |
| Hidden-taskbar | Each Simple app maps to its own host-native window | Simple taskbar hidden | Simple WM owns logical state; host owns native shells |

### SimpleOS mode

SimpleOS mode runs inside SimpleOS. The WM service uses the same logical
window/taskbar/session model as host mode, but the frontend uses SimpleOS
display/input backends and the Simple web engine where web UI is needed. The
Simple web backend still renders through the shared Simple 2D engine, so
SimpleOS and host mode do not fork the drawing model.

### UISession is the single entry for CLI, TUI, and GUI

All front-ends — textual and graphical — funnel through `UISession`
(`src/lib/common/ui/session.spl`). Its docstring is the contract:

> *"Central shared-state container that owns UIState, WidgetStore,
> Viewport, ChangeLog, LifecycleRegistry, and SurfaceManager. All state
> transitions flow through the session, enabling shared state across
> CLI, TUI, and GUI backends."*

Concretely, the siblings under `src/app/ui.*` are all **UISession
backends**, not a separate stack:

| Family | `ui.*` apps | Renders to |
|--------|-------------|-----------|
| Headless / test | `ui.none`, `ui.test_api`, `ui.render` | buffer / snapshot |
| CLI | `ui.cli`, `ui.ipc`, `ui.mcp`, `ui.vscode` | stdio / socket / LSP |
| TUI | `ui.tui`, `ui.tui_web` | terminal cells |
| GUI (pure Simple) | via `os.compositor` + `hosted_backend` / `fb_backend` | winit / framebuffer |
| GUI (Simple web) | `ui.browser`, `ui.web` | HTMLCanvas / WebGPU through Simple 2D |
| GUI (desktop host) | `ui.electron`, `ui.tauri` | BrowserWindow / host native window |

A backend implements the `backend.spl` trait (`common.ui.backend`) plus
the usual event-loop integration. The widget tree, diff, lifecycle, and
capability policy are identical for every backend — which is why the
CLI-mode observer in `ui.cli/observer.spl` and the baremetal compositor
consume the same `UIEvent` stream.

**Consequence for the drawing-layer variations** (plan doc):

- V1 (SimpleOS baremetal) and V2 (host OS) differ only below the
  `Compositor` line — swap `fb_backend` + `Ps2InputBackend` for
  `hosted_backend` + `HostedInputBackend`.
- V3 (Simple web / Chromium-class simple_browser) and V4 (Electron) swap the
  backend pair for `browser_compositor_backend` / `electron_capture` and
  translate DOM or IPC events into `os.gui.input_event`.
- The app, GUI Lib, WM service, and 2D engine are unchanged across all
  environments and presentation modes. That is the invariant this doc defends.

## Component Design

### 1. InputBackend Trait (NEW)
**File:** `src/os/compositor/input_backend.spl`

```simple
trait InputBackend:
    """Abstract input interface for compositor.
    Returns platform-independent key/mouse events."""
    fn poll_key() -> KeyEvent?
    fn poll_mouse() -> MouseEvent?
    fn alt_held() -> bool
    fn shift_held() -> bool
    fn ctrl_held() -> bool
    fn key_to_char(key: Key) -> text?
```

### 2. Ps2InputBackend (ADAPTER)
**File:** `src/os/compositor/input_backend.spl`

```simple
class Ps2InputBackend:
    keyboard: Ps2Keyboard
    mouse: Ps2Mouse

impl InputBackend for Ps2InputBackend:
    fn poll_key() -> KeyEvent?:
        self.keyboard.poll()
    fn poll_mouse() -> MouseEvent?:
        self.mouse.poll()
    ...
```

### 3. HostedInputBackend (NEW)
**File:** `src/os/compositor/hosted_input_backend.spl`

```simple
class HostedInputBackend:
    event_loop_id: i64
    _alt_held: bool
    _shift_held: bool
    _ctrl_held: bool

impl InputBackend for HostedInputBackend:
    fn poll_key() -> KeyEvent?:
        # Poll winit events, convert to KeyEvent
        val ev = rt_winit_event_loop_poll_events(self.event_loop_id, 1)
        ...
    fn poll_mouse() -> MouseEvent?:
        # Poll winit events, convert to MouseEvent
        ...
```

### 4. HostedCompositorBackend (NEW)
**File:** `src/os/compositor/hosted_backend.spl`

```simple
class HostedCompositorBackend:
    window_id: i64
    buffer_id: i64
    w: i32
    h: i32

impl CompositorBackend for HostedCompositorBackend:
    fn width() -> i32: self.w
    fn height() -> i32: self.h
    me clear(color: u32):
        rt_winit_buffer_fill_rect(self.buffer_id, 0, 0, self.w, self.h, color)
    me fill_rect(x, y, w, h, color):
        rt_winit_buffer_fill_rect(self.buffer_id, x, y, w, h, color)
    me draw_char_8x16(x, y, ch, fg, bg):
        # Use glyph data + put_pixel or native glyph rendering
    me present():
        rt_winit_buffer_present(self.window_id, self.buffer_id)
    me present_rect(x, y, w, h):
        rt_winit_buffer_present(self.window_id, self.buffer_id)
```

### 5. Compositor Refactor
**File:** `src/os/compositor/compositor.spl`

Change from:
```simple
class Compositor:
    fb: FramebufferDriver
    keyboard: Ps2Keyboard
    mouse: Ps2Mouse
```

To:
```simple
class Compositor:
    backend: CompositorBackend
    input: InputBackend
    cursor: CursorState
    ...
```

All `self.fb.fill_rect()` → `self.backend.fill_rect()`
All `self.keyboard.poll()` → `self.input.poll_key()`
All `self.mouse.poll()` → `self.input.poll_mouse()`

### 6. Entry Points

#### Baremetal (unchanged)
```simple
# examples/simple_os/arch/x86_64/gui_entry.spl
val fb = FramebufferDriver.from_boot_info(fb_info)
val backend = FbCompositorBackend.new(fb)
val input = Ps2InputBackend.new(Ps2Keyboard.new(), Ps2Mouse.create(...))
var compositor = Compositor.new(backend, input)
var shell = DesktopShell.new(compositor)
shell.run()
```

#### Hosted (all OS)
```simple
# src/os/hosted/hosted_entry.spl
val el = rt_winit_event_loop_new()
val win = rt_winit_window_new(el, 640, 480, "SimpleOS Desktop")
val buf = rt_winit_buffer_create(640, 480, 0xFF1A1B2E)
val backend = HostedCompositorBackend.new(win, buf, 640, 480)
val input = HostedInputBackend.new(el)
var compositor = Compositor.new(backend, input)
var shell = DesktopShell.new(compositor)
shell.run()
```

## File Layout

```
src/os/compositor/
  compositor.spl                   # Uses CompositorBackend + InputBackend traits
  display_backend.spl              # CompositorBackend trait + Fb/Gpu impls
  fb_backend.spl                   # V1: baremetal framebuffer backend
  hosted_backend.spl               # V2: HostedCompositorBackend (winit+softbuffer)
  hosted_input_backend.spl         # V2: HostedInputBackend (winit events)
  browser_backend.spl              # V3: Chromium/browser drawing backend
  browser_compositor_backend.spl   # V3: compositor wrapper for Browser
  electron_capture.spl             # V4: Electron BrowserWindow bridge
  input_backend.spl                # InputBackend trait + Ps2InputBackend
  compositor_engine2d.spl          # Bridge to lib.gc_async_mut.gpu.engine2d
  engine2d_display.spl             # Engine2D → display backend adapter
  decorations.spl · cursor.spl · layout_manager.spl · snap.spl
  glass_effects.spl · glass_effects_pure.spl · glass_port.spl
  wm_scene.spl · wm_consistency_runner.spl
  perceptual_compare.spl · screenshot_compare.spl · diff_export.spl
  qemu_capture.spl                 # Capture for sys-gui baselines

src/os/gui/
  mod.spl · render.spl · input_event.spl · shortcut.spl

src/os/desktop/
  shell.spl · dock.spl · app_switcher.spl
  app_manifest.spl · notification_center.spl · mod.spl

src/lib/common/ui/                 # GUI Lib — shared by all backends
  session.spl · widget.spl · widget_store.spl · builder.spl
  layout.spl · layout_engine.spl · diff.spl · patch.spl
  state.spl · event.spl · lifecycle.spl · changelog.spl
  surface.spl · viewport.spl · profile.spl · capability.spl
  capability_policy.spl · theme · async_* · backend.spl · backend_factory.spl

src/lib/common/render_scene/       # 2D engine trait + executor
  engine_trait.spl · engine_float.spl · engine_int.spl
  engine2d_executor.spl · executor.spl · scene.spl

src/lib/gc_async_mut/gpu/engine2d/ # 2D engine backends
  engine.spl · compositor.spl · color.spl · glyph.spl
  backend_cpu.spl · backend_software.spl · backend_baremetal.spl
  backend_virtio_gpu.spl · backend_vulkan.spl · backend_metal.spl
  backend_opengl.spl · backend_cuda.spl · backend_rocm.spl · backend_intel.spl

src/app/ui.*                       # UISession backends (see table above)
  ui.none · ui.cli · ui.tui · ui.tui_web · ui.render · ui.test_api
  ui.browser · ui.web · ui.electron · ui.tauri · ui.ipc · ui.mcp · ui.vscode

src/app/wm_compare/                # Cross-backend parity harness
  main.spl · scene_registry.spl · live_capture.spl · html_compat.spl
```

## Platform Support Matrix

| Variation | Environment | Presentation | Compositor Backend | Input Backend | Surface | 2D Engine Backend | Status |
|-----------|-------------|--------------|--------------------|---------------|---------|-------------------|--------|
| V1 | SimpleOS / baremetal x86_64 | Embedded desktop | `fb_backend` | `Ps2InputBackend` | BGA framebuffer | `backend_software` / `backend_baremetal` | sys-gui-006 baseline |
| V1 | SimpleOS / baremetal x86_64 + VirtIO | Embedded desktop | `display_backend` (GPU) | `Ps2InputBackend` | VirtIO-GPU | `backend_virtio_gpu` | sys-gui-007 in progress |
| V2 | Host macOS | Embedded / Native / Hidden-taskbar | `hosted_backend` | `hosted_input_backend` | winit+softbuffer → Cocoa | `backend_metal` / `backend_cpu` | hosted path green; Metal WIP |
| V2 | Host Linux | Embedded / Native / Hidden-taskbar | `hosted_backend` | `hosted_input_backend` | winit+softbuffer → X11/Wayland | `backend_vulkan` / `backend_cpu` | hosted path green |
| V2 | Host Windows | Embedded / Native / Hidden-taskbar | `hosted_backend` | `hosted_input_backend` | winit+softbuffer → Win32 | `backend_cpu` (DX WIP) | hosted shim WIP |
| V2 | Host FreeBSD | Embedded / Native / Hidden-taskbar | `hosted_backend` | `hosted_input_backend` | winit+softbuffer → Xlib | `backend_cpu` | exists, untested |
| V3 | Host or SimpleOS Simple web | Embedded / web surface | `browser_compositor_backend` + `browser_backend` | DOM → `input_event` | HTMLCanvas / WebGPU | shared Simple 2D engine via `backend_software` / `backend_webgpu` | ✅ Row 5 Done 2026-04-14 — M1–M12 landed, wm_compare parity green, Acid2 passes |
| V4 | Host Electron | Embedded / Native / Hidden-taskbar | `browser_compositor_backend` + `electron_capture` | IPC → `input_event` | BrowserWindow (main+renderer) | shared Simple 2D engine via `backend_software` | advisory/dev-preview; unit state covered, live OS smoke not default CI |

See [`doc/03_plan/gui_drawing_layer_variations.md`](../03_plan/gui_drawing_layer_variations.md)
for the restored handoff and current gap summary.

## FFI Coverage Matrix

The hosted runtime (`src/runtime/hosted/`) exports `rt_*` SFFI primitives for
per-platform native surfaces and optional GPU/JS backends. Every symbol has a
stub implementation compiled by default; opting into a real backend requires
the corresponding Cargo feature flag, which also enables the optional crate
dependency:

| Feature flag     | Crate dependency pulled in | Symbols affected              |
|------------------|----------------------------|-------------------------------|
| `cocoa-real`     | `objc2-app-kit`            | `rt_cocoa_*`                  |
| `win32-real`     | `windows-sys`              | `rt_win32_*`                  |
| `webgpu-real`    | `wgpu` + `pollster`        | `rt_webgpu_*`                 |
| `test262-real`   | `rquickjs`                 | `rt_test262_eval`, `_list_cases`, `_case_path` |

Legend: ✅ real — 🟡 stub — ❌ unavailable (feature/platform mismatch at link time).

| Primitive                       | Linux | macOS | Windows | FreeBSD | Feature flag   | Status                          |
|---------------------------------|:-----:|:-----:|:-------:|:-------:|----------------|---------------------------------|
| **Cocoa surface**               |       |       |         |         |                |                                 |
| `rt_cocoa_window_new`           | ❌    | ✅    | ❌      | ❌      | `cocoa-real`   | NSWindow + NSImageView          |
| `rt_cocoa_window_resize`        | ❌    | ✅    | ❌      | ❌      | `cocoa-real`   |                                 |
| `rt_cocoa_window_close`         | ❌    | ✅    | ❌      | ❌      | `cocoa-real`   |                                 |
| `rt_cocoa_event_pump`           | ❌    | ✅    | ❌      | ❌      | `cocoa-real`   | NSRunLoop tick                  |
| `rt_cocoa_layer_create`         | ❌    | ✅    | ❌      | ❌      | `cocoa-real`   | NSBitmapImageRep                |
| `rt_cocoa_layer_free`           | ❌    | ✅    | ❌      | ❌      | `cocoa-real`   |                                 |
| `rt_cocoa_layer_present`        | ❌    | ✅    | ❌      | ❌      | `cocoa-real`   | blit to NSImageView             |
| `rt_cocoa_layer_fill_rect`      | ❌    | ✅    | ❌      | ❌      | `cocoa-real`   |                                 |
| `rt_cocoa_layer_blend_rect`     | ❌    | ✅    | ❌      | ❌      | `cocoa-real`   |                                 |
| `rt_cocoa_layer_gradient_v`     | ❌    | ✅    | ❌      | ❌      | `cocoa-real`   |                                 |
| `rt_cocoa_layer_blur`           | ❌    | ✅    | ❌      | ❌      | `cocoa-real`   | CPU 3×3 box kernel              |
| `rt_cocoa_layer_read_pixel`     | ❌    | ✅    | ❌      | ❌      | `cocoa-real`   |                                 |
| **Win32 surface**               |       |       |         |         |                |                                 |
| `rt_win32_window_new`           | ❌    | ❌    | ✅      | ❌      | `win32-real`   | HWND via CreateWindowExW        |
| `rt_win32_window_resize`        | ❌    | ❌    | ✅      | ❌      | `win32-real`   |                                 |
| `rt_win32_window_close`         | ❌    | ❌    | ✅      | ❌      | `win32-real`   |                                 |
| `rt_win32_message_pump`         | ❌    | ❌    | ✅      | ❌      | `win32-real`   | PeekMessage tick                |
| `rt_win32_dib_create`           | ❌    | ❌    | ✅      | ❌      | `win32-real`   | CreateDIBSection                |
| `rt_win32_dib_free`             | ❌    | ❌    | ✅      | ❌      | `win32-real`   |                                 |
| `rt_win32_dib_resize`           | ❌    | ❌    | ✅      | ❌      | `win32-real`   |                                 |
| `rt_win32_dib_present`          | ❌    | ❌    | ✅      | ❌      | `win32-real`   | BitBlt to HWND DC               |
| `rt_win32_dib_present_rect`     | ❌    | ❌    | ✅      | ❌      | `win32-real`   |                                 |
| `rt_win32_dib_fill_rect`        | ❌    | ❌    | ✅      | ❌      | `win32-real`   |                                 |
| `rt_win32_dib_blend_rect`       | ❌    | ❌    | ✅      | ❌      | `win32-real`   |                                 |
| `rt_win32_dib_gradient_v`       | ❌    | ❌    | ✅      | ❌      | `win32-real`   |                                 |
| `rt_win32_dib_blur`             | ❌    | ❌    | ✅      | ❌      | `win32-real`   | CPU 3×3 box kernel              |
| `rt_win32_dib_read_pixel`       | ❌    | ❌    | ✅      | ❌      | `win32-real`   |                                 |
| **WebGPU**                      |       |       |         |         |                |                                 |
| `rt_webgpu_is_available`        | 🟡/✅ | 🟡/✅ | 🟡/✅   | 🟡/✅   | `webgpu-real`  | wgpu adapter probe when real    |
| `rt_webgpu_init`                | 🟡/✅ | 🟡/✅ | 🟡/✅   | 🟡/✅   | `webgpu-real`  | Instance + Adapter + Device     |
| `rt_webgpu_shutdown`            | 🟡/✅ | 🟡/✅ | 🟡/✅   | 🟡/✅   | `webgpu-real`  |                                 |
| `rt_webgpu_create_surface`      | 🟡/✅ | 🟡/✅ | 🟡/✅   | 🟡/✅   | `webgpu-real`  |                                 |
| `rt_webgpu_destroy_surface`     | 🟡/✅ | 🟡/✅ | 🟡/✅   | 🟡/✅   | `webgpu-real`  |                                 |
| `rt_webgpu_upload_pixels`       | 🟡/✅ | 🟡/✅ | 🟡/✅   | 🟡/✅   | `webgpu-real`  | writeTexture fallback           |
| `rt_webgpu_present`             | 🟡/✅ | 🟡/✅ | 🟡/✅   | 🟡/✅   | `webgpu-real`  | compute-draw shader when real   |
| **JS / test262**                |       |       |         |         |                |                                 |
| `rt_test262_eval`               | 🟡/✅ | 🟡/✅ | 🟡/✅   | 🟡/✅   | `test262-real` | rquickjs when real              |
| `rt_test262_list_cases`         | 🟡/✅ | 🟡/✅ | 🟡/✅   | 🟡/✅   | `test262-real` | directory walk when real        |
| `rt_test262_case_path`          | 🟡/✅ | 🟡/✅ | 🟡/✅   | 🟡/✅   | `test262-real` | thread-local corpus when real   |
| `rt_test262_load_corpus`        | 🟡    | 🟡    | 🟡      | 🟡      | —              | stub until corpus manifest lands |
| `rt_test262_case_source`        | 🟡    | 🟡    | 🟡      | 🟡      | —              |                                 |
| `rt_test262_case_negative`      | 🟡    | 🟡    | 🟡      | 🟡      | —              |                                 |
| `rt_test262_case_count`         | 🟡    | 🟡    | 🟡      | 🟡      | —              |                                 |
| `rt_test262_corpus_free`        | 🟡    | 🟡    | 🟡      | 🟡      | —              |                                 |

Linux and FreeBSD use `winit_ffi` for native surfaces; Cocoa and Win32 entries are
❌ on the other platforms because the corresponding crates do not link there.
WebGPU is cross-platform so it lists both stub (🟡) and real (✅) outcomes — the
effective state depends on whether `webgpu-real` is enabled at build time.

## Winit FFI Functions Used

Already in `winit_ffi.rs`:
- `rt_winit_event_loop_new/free/poll_events`
- `rt_winit_window_new/free/present_rgba`
- `rt_winit_event_get_type/keyboard_input/mouse_moved/mouse_button/free`
- `rt_winit_buffer_create/fill_rect/present/free` (native pixel buffer)
- `rt_thread_sleep`

No new Rust FFI needed — existing functions cover all requirements.

## Migration Plan

Steps 1–7 below describe the original V1↔V2 cutover and are **done**.
The active tracker for V3/V4 and remaining V2 host surfaces lives in
[`doc/03_plan/gui_drawing_layer_variations.md`](../03_plan/gui_drawing_layer_variations.md).

1. ✅ Create `InputBackend` trait + `Ps2InputBackend` adapter
2. ✅ Create `HostedInputBackend` wrapping winit events
3. ✅ Create `HostedCompositorBackend` wrapping winit buffer functions
4. ✅ Refactor `Compositor` to use trait objects instead of concrete types
5. ✅ Create `hosted_entry.spl` that wires hosted backends to Compositor+DesktopShell
6. ◻ Verify all existing apps (Calculator, Terminal, etc.) work unchanged on V2
7. ◻ Test on macOS, Linux, Windows, FreeBSD — tracked per platform in sys-gui-*

### Next phases (tracked in the plan doc)

8. Lock `Compositor` + `Engine2D` trait surfaces; document in `gui_layer_contract.md`
9. Expand `wm_compare` to run the same scene through V1/V2 and diff
10. Land Cocoa + Win32 hosted surfaces behind `hosted_backend`
11. virtio-gpu accelerated path in QEMU for V1 (sys-gui-008)
12. CEF or simple_browser shell driving `browser_compositor_backend` (V3)
13. Electron main/renderer split via `electron_capture` + `ui.ipc` (V4)
14. Shared input-event conformance suite across all four variations
15. Golden-image gate: same app, 4 backends, ≤1% perceptual diff
