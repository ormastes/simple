# Simple GUI Internal Window Implementation Spec

Status: bridge implemented (2026-07-06); chrome/content/taskbar drawing moved
into a common.ui CompositorBackend executor, plus chrome-kind (titled /
borderless) and background-provider support (2026-07-07). A fuller Draw IR
executor can replace the current framebuffer executor later without changing
the Simple GUI scene contract.

## Goal

The WM must use the Simple GUI core for internal windows. Host WM and SimpleOS
WM must differ only in backend/config glue; they must not keep separate dummy
or evidence-only window renderers.

## Implemented Bridge

- `src/lib/common/ui/window_scene.spl` now exposes:
  - `simple_gui_internal_window(...)`
  - `simple_gui_internal_window_scene(...)`
  - `simple_gui_internal_window_renderer_handoff_marker()`
- `src/os/compositor/shared_mdi_framebuffer_scene.spl` now converts MDI seed and
  lifecycle windows through `SharedWmScene` before rendering framebuffer pixels.
- SimpleOS/QEMU framebuffer rendering consumes `SharedWmScene` through
  `render_shared_mdi_framebuffer_scene_for_simple_gui_scene(...)`.
- Host WM fallback chrome/taskbar rendering projects hosted windows into
  `SharedWmScene` with `shared_mdi_scene_from_render_windows(...)` and renders
  scene-derived window chrome/taskbar while preserving host-only content
  scroll/cache state.
- The live host WM taskbar demo opens through the `GuiRenderer` facade and the
  `spl_winit` SFFI library. App code must not import raw
  `std.io.window_winit` or call raw `rt_winit_*` externs for this lane.

## Follow-up Implementation (2026-07-07 update)

1. **Done.** Chrome/content/taskbar drawing moved out of
   `shared_mdi_framebuffer_scene.spl` into a `common.ui` executor:
   `common.ui.window_scene_draw_ir.shared_wm_scene_render_to_backend(backend,
   scene)` renders a `SharedWmScene` directly against any
   `os.compositor.display_backend.CompositorBackend` draw target (desktop
   chrome, per-window chrome/content, taskbar). `shared_mdi_framebuffer_scene.spl`
   is now glue: it builds the `SharedWmScene` (as before) and calls the
   executor; the legacy `SharedMdiRenderWindow`-shaped entrypoints
   (`render_shared_mdi_desktop_chrome`, `draw_shared_mdi_window_chrome`,
   `draw_shared_mdi_taskbar`, `render_shared_mdi_app_content`,
   `render_shared_mdi_windows_to_backend`) still exist and delegate to the
   executor, unchanged for existing callers (e.g.
   `os.compositor.host_compositor_entry.spl`). Taskbar item geometry
   (`wm_taskbar_item_width`/`wm_taskbar_dock_width`/`wm_taskbar_item_x`) moved
   from `os.compositor.wm_action_applier` into `common.ui.window_scene_draw_ir`
   (pure math, no os dependency needed by the executor); `wm_action_applier`
   re-exports the same names so its callers are unaffected.
2. **Done.** The x86_64 QEMU entry (`gui_entry_engine2d.spl`) and the host WM
   capture-evidence path both call the same
   `render_shared_mdi_framebuffer_scene*` functions in
   `shared_mdi_framebuffer_scene.spl`, which now both route through the one
   `shared_wm_scene_render_to_backend` executor. No changes were needed in
   either lane entry file — the signature-compatible glue refactor made both
   lanes share the executor automatically.
3. Preserve current readable-text evidence. Do not replace it with a fake,
   smaller framebuffer, dummy window labels, or reduced-resolution shortcut.
   (Still true; unchanged by this update — see
   `check-simpleos-wm-visible-display-evidence.shs`.)

## Chrome-Kind and Background Extension Contract (2026-07-07)

- `SharedWmWindow.chrome_kind` (`common.ui.window_scene`) is `"titled"`
  (default, standard title bar + border) or `"borderless"` (pure content
  surface for taskbar-like windows and plain drawn objects — no titlebar
  chrome pixels; z-order/focus/hit-test bounds are unchanged). Every
  `SharedWmWindow` construction site sets it explicitly or gets it via
  `simple_gui_internal_window(...)`'s default, so existing callers/bridges are
  unaffected. The executor gates the title bar/border draw call on this field
  only; content-area geometry also widens to the full window bounds for
  borderless windows (no chrome inset).
- `SharedWmScene.background: BackgroundSpec` (`kind`, `color`, `source`) is a
  provider contract, not a hardcoded fill. `kind: "color"` is implemented;
  `"image"` and `"motion"` are reserved names for later providers.
  `shared_wm_scene_resolve_background(...)` is the single resolution point:
  unknown/unimplemented kinds never silently fall back to a default fill —
  they log a diagnostic and return `resolved: false` plus the loud
  `WM_BACKGROUND_UNRESOLVED_MARKER_COLOR` (`0xFFFF00FF`) so a caller/executor
  visibly shows the failure instead of masking it. Callers that only need a
  solid color today (`shared_wm_background_color(color)`) do not need to
  change when image/motion providers land later — only
  `shared_wm_scene_resolve_background` gains a new `if` branch.

## Verification

Run after implementation:

```sh
bin/simple check src/lib/common/ui/window_scene.spl
bin/simple check src/os/compositor/shared_mdi_framebuffer_scene.spl
bin/simple check src/lib/nogc_sync_mut/ui/gui_renderer.spl
bin/simple check src/os/compositor/hosted_backend_gui_renderer.spl
bin/simple check src/os/compositor/host_compositor_entry.spl
SIMPLE_BIN=bin/simple BUILD_DIR=build/wm_multiapp_taskbar_gui_renderer WM_MULTIAPP_TIMEOUT_SECS=180 sh scripts/check/check-wm-multiapp-taskbar-evidence.shs
SIMPLE_BIN=bin/simple BUILD_DIR=build/hosted_wm_capture_simple_gui_shared sh scripts/check/check-hosted-wm-capture-evidence.shs
SIMPLE_BIN=bin/simple BUILD_DIR=build/simpleos_wm_visible_display_simple_gui_shared SIMPLEOS_WM_VISIBLE_MARKER_TIMEOUT_SECS=120 sh scripts/check/check-simpleos-wm-visible-display-evidence.shs
SIMPLE_BIN=bin/simple BUILD_DIR=build/simpleos_wm_qmp_drag_delta_simple_gui_shared SIMPLEOS_WM_QMP_LAUNCH_TIMEOUT_MS=120000 sh scripts/check/check-simpleos-wm-qmp-drag-delta-evidence.shs
```

The QEMU visible-display gate should continue to validate readable title glyphs,
not only nonblack/color/taskbar pixels.
The host multi-app taskbar gate should continue to validate app launch,
taskbar focus/minimize/restore, readable title text, close-button pixels, and
captured real-window frames through the self-hosted Simple binary plus
`SIMPLE_SPL_WINIT_PATH`, not a Rust seed GUI driver.
