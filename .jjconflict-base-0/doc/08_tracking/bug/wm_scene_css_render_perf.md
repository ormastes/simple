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

## Fix directions (not done here)

- Profile `web_render_pixel_backend` / `simple_web_html_layout_renderer` to
  find the ~6 s fixed cost (likely style extraction / `compute_styles` /
  `apply_decls` over the very large chrome stylesheet).
- Cache the parsed stylesheet + computed style tree across presents (chrome CSS
  is static; only element geometry changes frame to frame).
- Or JIT/native-compile the CSS raster hot path so the cap can be raised to
  cover desktop resolutions.

## Workaround in place

`src/os/compositor/wm_scene.spl`:
- `WM_SCENE_CSS_RENDER_PIXEL_CAP = 10000` gates the CSS path.
- The `render_scene_to_backend` fallback now rasterizes the actual
  `SceneElement` rects (painter's order, theme desktop background base) so
  themed chrome still appears above the cap.
