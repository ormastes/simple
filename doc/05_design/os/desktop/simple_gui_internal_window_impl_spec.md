# Simple GUI Internal Window Implementation Spec

Status: bridge implemented, 2026-07-06. A fuller Draw IR executor can replace
the current framebuffer executor later without changing the Simple GUI scene
contract.

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

## Follow-up Implementation

1. Move more chrome/content drawing out of
   `shared_mdi_framebuffer_scene.spl` into a `common.ui` framebuffer or Draw IR
   executor when that layer can depend on a backend-neutral draw target.
2. Keep QEMU SimpleOS fullscreen and host WM evidence on the same scene/render
   model.
3. Preserve current readable-text evidence. Do not replace it with a fake,
   smaller framebuffer, dummy window labels, or reduced-resolution shortcut.

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
