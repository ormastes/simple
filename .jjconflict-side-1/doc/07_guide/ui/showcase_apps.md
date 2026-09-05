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

## Spec wiring (landed, still RED — 2026-07-14)

`test/03_system/os/showcase/showcase_apps_spec.spl`'s five wrapper helpers (`launch_showcase`, `require_installed_identity`, `require_owned_window`, `require_nonblank_frame`, `require_post_input_change`) now route through the production adapter — `common.ui.showcase_catalog` readiness flags gate every call, and `os.hosted.hosted_wm_evidence` (`host_wm_evidence_config_from_env`, `host_wm_evidence_parse_command`) supplies the evidence-config/capture/snapshot/input-FIFO checks — instead of a bare `fail()`. All nine app/surface cases still fail, now with a structured `app=... surface=... phase=... cause=surface-not-ready detail=...` message, because every readiness flag above is still `false`; they only flip once a surface has deployed proof.

## 2D feature coverage (graphics_2d_showcase vs Engine2D API)

`draw_showcase()` in `examples/06_io/ui/graphics_2d_showcase.spl` exercises 35
of the 38 public drawing/composition methods on `Engine2D`
(`src/lib/gc_async_mut/gpu/engine2d/engine.spl`) — essentially the full
primitive surface: fill/stroke/thick rect, rounded rect (filled+outline),
line, polyline, circle/ellipse (stroke+filled+thick), arc, triangle
(filled+outline), polygon, cubic bezier, gradients (linear-vertical,
linear-horizontal, radial), image ops (blit, blend, scaled,
affine-transform), text (plain+background), alpha blend + blend-mode, clip,
alpha mask, shadow, blur, and engine-to-engine composition (plain + opacity).

**Not shown (exist on `Engine2D` but absent from the showcase):**
- `draw_glyph_run` — raw pre-shaped glyph-batch rendering (the showcase only
  calls the higher-level `draw_text` / `draw_text_bg`)
- Font management (`load_font`, `load_font_bytes`, `select_font_identity`,
  `unload_font`, `font_cache_stats`) — the showcase never loads a custom font
- `tick_forever` — the frame-pacing animation loop; the showcase renders one
  static frame and never enters a paced loop

**Not offered by `Engine2D` at all** (so the showcase cannot demonstrate them
without a runtime feature add): a dedicated anti-aliasing toggle/primitive,
dashed/patterned strokes, and general (non-image) shape rotation/scaling —
`draw_image_transform` is the only affine-transform primitive and it is
image-only.
