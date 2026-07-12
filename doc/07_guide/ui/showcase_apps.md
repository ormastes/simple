# Running the GUI, web, and 2D showcases

The canonical app IDs are `graphics_2d_showcase`, `web_standards_showcase`, and `gui_widget_showcase`. Readiness is recorded in `src/lib/common/ui/showcase_catalog.spl`; a false entry means the surface is not yet accepted even if an older demo window exists.

## Standalone

```text
scripts/gui/macos-gui-run.shs examples/06_io/ui/graphics_2d_showcase_gui.spl
scripts/gui/macos-gui-run.shs examples/06_io/ui/web_standards_showcase_gui.spl
SIMPLE_GUI=1 scripts/gui/macos-gui-run.shs examples/06_io/ui/widget_showcase_gui.spl
```

On Linux, use `scripts/gui/linux-gui-run.shs` with the same source/page arguments. The graphics and web entries currently remain blocked by the recorded nil-receiver runtime failures; the commands are reproductions, not PASS claims.

## Host WM

The accepted existing host-WM entry is:

```text
SIMPLE_GUI=1 scripts/gui/macos-gui-run.shs examples/06_io/ui/wm_widget_showcase_gui.spl
```

Host-WM graphics and web catalog adapters are not yet accepted. Do not substitute the static shape demo or a background-only browser surface.

## SimpleOS/QEMU

No showcase entry is accepted in the installed SimpleOS launcher yet. A valid result must show the installed `/sys/apps/*_showcase.smf` identity, guest PID/window ownership, nonblank guest framebuffer, and a post-input state/pixel change. Host wrappers and fixed serial markers are insufficient.

## Verification flow

For each ready surface: open the catalog, launch the app, snapshot the visible window, find a labeled control/section, act through the real input route, inspect event history, capture the post-action semantic state, and retain the same-run framebuffer/readback plus backend provenance. Blank frames, source-only assertions, synthetic GPU handles, and action logs without a changed frame/state fail verification.
