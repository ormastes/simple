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
- Existing host and QEMU callers can keep using the legacy
  `SharedMdiRenderWindow` entrypoints while the internal boundary is
  `common.ui.window_scene`.

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
SIMPLE_BIN=bin/simple BUILD_DIR=build/hosted_wm_capture_simple_gui_shared sh scripts/check/check-hosted-wm-capture-evidence.shs
SIMPLE_BIN=bin/simple BUILD_DIR=build/simpleos_wm_visible_display_simple_gui_shared SIMPLEOS_WM_VISIBLE_MARKER_TIMEOUT_SECS=120 sh scripts/check/check-simpleos-wm-visible-display-evidence.shs
SIMPLE_BIN=bin/simple BUILD_DIR=build/simpleos_wm_qmp_drag_delta_simple_gui_shared SIMPLEOS_WM_QMP_LAUNCH_TIMEOUT_MS=120000 sh scripts/check/check-simpleos-wm-qmp-drag-delta-evidence.shs
```

The QEMU visible-display gate should continue to validate readable title glyphs,
not only nonblack/color/taskbar pixels.
