---
id: wm_scene_css_render_perf
status: OPEN
severity: medium
discovered: 2026-07-02
discovered_by: WM chrome theming work — render_scene_to_backend perf probe (1024x768)
related: src/os/compositor/wm_scene.spl
related: src/os/compositor/web_render_surface.spl
related: src/lib/gc_async_mut/ui/web_render_pixel_backend.spl
related: src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl
---

# WM scene CSS pixel render is too slow for desktop resolutions

**Status:** OPEN. Worked around by capping the CSS path at
`WM_SCENE_CSS_RENDER_PIXEL_CAP = 10000` px in `render_scene_to_backend`; larger
scenes use a direct-rect rasterizer fallback (which now paints the real scene
elements instead of a near-blank fill).

## Summary

`wm_scene.scene_to_html()` + `compositor_render_html_pixels()` render the WM
chrome through the real pure-Simple CSS engine, which is the only path that
applies the `<style>` classes (`.bar` / `.glass` / titlebar / taskbar). Under
the interpreter this path is far too slow to run per scene present at real
window-manager resolutions, so `render_scene_to_backend` skips it above a
10000px cap. That means CSS-styled chrome is effectively dead at desktop
resolutions.

## Measured cost

Measured on this machine via `bin/simple run --mode=interpreter`, rendering
`standard_wm_scene(w,h)` through `scene_to_html` + `compositor_render_html_pixels`:

| size      | pixels  | render time |
|-----------|---------|-------------|
| 100x100   | 10000   | ~6.2 s      |
| 160x120   | 19200   | ~6.7 s      |
| 200x150   | 30000   | ~7.5 s      |
| 320x200   | 64000   | ~10.3 s     |
| 1024x768  | 786432  | > 2 min (timed out) |

There is a large (~6 s) fixed cost even at the 10000px cap boundary (dominated
by parsing/applying the large inline stylesheet emitted by `scene_to_html`),
plus roughly linear per-pixel growth. Extrapolated to 1024x768 the render is
minutes long — unusable for a live compositor present loop.

## Impact

- CSS-styled WM chrome (glass titlebars, blur, rounded corners) only renders
  for tiny scenes (<= 10000px), i.e. test fixtures. At real resolutions the
  fallback paints solid-colored element rects — correct layout and colors, but
  none of the CSS material/effects.
- Raising the cap is not viable today: even the current cap admits a ~6 s
  render.

## Native fast path added (2026-07-03) — CSS chrome now renders above the cap

The dominant cost above the cap was **not** the CSS engine itself but the
per-op interpreted framebuffer mirror inside Engine2D/backends (see
`doc/08_tracking/bug/engine2d_interpreted_mirror_dominates_render_2026-07-03.md`).
That mirror is now bypassed by a no-mirror native fast path:

- `Engine2D.create_with_backend_fast()` shrinks the Metal CPU mirror to 1x1 so
  draw ops forward to the GPU only, and `read_pixels()` downloads the GPU
  framebuffer in a single FFI hop (`rt_metal_buffer_download` ptr +
  `rt_bytes_from_raw`, packed to `[u32]` with no per-element FFI).
- `simple_web_layout_render_html_pixels_engine2d()` runs the real layout Draw IR
  (`simple_web_layout_render_html_draw_ir`) on that fast engine.
- `render_scene_to_backend`, above `WM_SCENE_CSS_RENDER_PIXEL_CAP`, now routes
  `scene_to_html(scene)` through that entry **first** (only when Metal is
  available), falling back to the themed direct-rect rasterizer otherwise. The
  `<= cap` CSS path is unchanged.

### Measured (M4, interpreter, 1024x768, 12-window WM scene)

| stage                       | native fast path |
|-----------------------------|------------------|
| layout + Draw IR generation | ~1.0 s (per-node; unchanged, not mirror-bound) |
| Engine2D fast create (Metal)| ~0.30 s          |
| clear                       | ~0.01 s          |
| **exec + one-shot readback**| **~1.4 s**       |
| **total (entry)**           | **~2.7 s**       |

The `exec + readback` cost meets the ≤2 s target (down from ~28 s: exec 17.9 s +
readback 10.1 s on the mirror path). Total including layout Draw IR generation is
~2.7 s; the remaining ~1 s is the layout pass (per-node, resolution-independent),
tracked separately from the mirror bug. Correctness: bit-exact vs the software
mirror for well-formed in-bounds rect scenes (evidence gate below); off-canvas
border clamping and GPU 5x7 vs CPU text remain small GPU-vs-CPU discrepancies not
covered by the cpu-metal primitive parity gate.

Evidence: `scripts/check/check-engine2d-nomirror-fast-render-evidence.shs`
(harness `test/02_integration/rendering/engine2d_nomirror_fast_render_run.spl`).

## Fix directions (remaining)

- Reduce the ~1 s layout Draw IR generation (per-node cost) — cache parsed
  stylesheet + computed style tree across presents (chrome CSS is static).
- GPU-side rectangular clip + text parity so sub-framebuffer clips and text are
  bit-exact under the fast path (today a sub-framebuffer clip falls back to the
  mirror; the full-framebuffer clip the layout emits is a no-op and stays GPU).

## Workaround still in place for non-Metal / sub-cap

`src/os/compositor/wm_scene.spl`:
- `WM_SCENE_CSS_RENDER_PIXEL_CAP = 10000` still gates the interpreted CSS path.
- Above the cap, when Metal is unavailable, `render_scene_to_backend` rasterizes
  the actual `SceneElement` rects (painter's order, theme desktop background
  base) so themed chrome still appears.
