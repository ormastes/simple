# Draw IR text lane ignores `letter-spacing`, `word-spacing` and `text-shadow`

- **Found:** 2026-11-19, while routing bare-text pages onto the Draw IR text lane.
- **Status:** open.
- **Where:** the Draw IR executor (`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`). The composer already emits the three as style props (`simple_web_html_layout_renderer_paint_draw_ir.spl`, `draw_ir_style_prop("letter-spacing", ...)`, `("text-shadow", ...)`); nothing reads them when the run is drawn. The raster lane (`simple_web_html_layout_renderer_paint_raster.spl`) paints all three.

## Measured

`simple_web_render_html_to_pixels_with_engine2d_backend(page, 128, 32, "cpu_simd")`, `<p style="margin:0;font-size:16px;color:#111827">`, ink = a channel under 200:

| page | ink bbox | note |
|---|---|---|
| `SPACING` | 0,3..66,13 | |
| `SPACING`, `letter-spacing:2px` | 0,3..66,13 | same pixels |
| `A B C` | 0,3..39,13 | |
| `A B C`, `word-spacing:6px` | 0,3..39,13 | same pixels |
| `SPACING`, `text-shadow:4px 3px #dc2626` | 0,3..66,13 | 0 pixels of `#dc2626` |

`text-indent`, `direction:rtl`, `text-overflow:ellipsis`, `text-transform` and `text-decoration-color` do paint on this lane.

## Consequence today

`_simple_web_engine2d_raster_only_text_property` (`simple_web_engine2d_renderer.spl`) keeps a bare-text page that authors one of the three on the raster lane, so it still paints them, in grayscale. A page with a `<p>` / `<span>` / heading takes the Draw IR lane and loses them.

## Fix

Apply the three in the Draw IR run painter (pen advance per glyph and per space; a shadow run under the glyph run), measure against Chrome 159, then delete `_simple_web_engine2d_raster_only_text_property` and the three `letter-spacing: 0px` / `word-spacing: 0px` / `text-shadow: none` plain pages in `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl`.
