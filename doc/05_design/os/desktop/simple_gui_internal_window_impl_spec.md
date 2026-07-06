# Simple GUI Internal Window Implementation Spec

Status: handoff for next WM/SimpleOS agent, 2026-07-06.

## Goal

The WM must use the Simple GUI core for internal windows. Host WM and SimpleOS
WM must differ only in backend/config glue; they must not keep separate dummy
or evidence-only window renderers.

## Current Handoff

- `src/lib/common/ui/window_scene.spl` now exposes:
  - `simple_gui_internal_window(...)`
  - `simple_gui_internal_window_scene(...)`
  - `simple_gui_internal_window_renderer_handoff_marker()`
- The marker is intentionally a handoff marker, not the final renderer API.
- `src/os/compositor/shared_mdi_framebuffer_scene.spl` still owns too much
  scene/window drawing logic. The next change should make it consume
  `SharedWmScene` from `common.ui.window_scene`.

## Required Implementation

1. Add a Simple GUI drawing facade for internal windows under `common.ui`, or
   extend `window_scene_draw_ir.spl` with a framebuffer/CompositorBackend
   executor if that fits the existing Draw IR path.
2. Convert `shared_mdi_seed_windows()` to create `SharedWmWindow` values through
   `simple_gui_internal_window(...)`.
3. Convert `render_shared_mdi_framebuffer_scene_for_windows(...)` and lifecycle
   rendering to consume `SharedWmScene` through the Simple GUI facade.
4. Keep QEMU SimpleOS fullscreen and host WM evidence on the same scene/render
   model.
5. Preserve current readable-text evidence. Do not replace it with a fake,
   smaller framebuffer, dummy window labels, or reduced-resolution shortcut.

## Verification

Run after implementation:

```sh
bin/simple check src/lib/common/ui/window_scene.spl
bin/simple check src/os/compositor/shared_mdi_framebuffer_scene.spl
SIMPLE_BIN=bin/simple BUILD_DIR=build/hosted_wm_capture_simple_gui_shared sh scripts/check/check-hosted-wm-capture-evidence.shs
SIMPLE_BIN=bin/simple BUILD_DIR=build/simpleos_wm_visible_display_simple_gui_shared SIMPLEOS_WM_VISIBLE_MARKER_TIMEOUT_SECS=120 sh scripts/check/check-simpleos-wm-visible-display-evidence.shs
SIMPLE_BIN=bin/simple BUILD_DIR=build/simpleos_wm_qmp_drag_delta_simple_gui_shared SIMPLEOS_WM_QMP_LAUNCH_TIMEOUT_MS=120000 sh scripts/check/check-simpleos-wm-qmp-drag-delta-evidence.shs
```

The QEMU visible-display gate should continue to validate readable title glyphs,
not only nonblack/color/taskbar pixels.
