# raster backend: unhinted gray glyph rasterizer, ink rows off Chrome at whole and fractional sizes

Date: 2026-11-19. Base: origin/release/1.0.0 6b65999ae66. Chrome 159.0.8154.6, 1x.

The software `raster` lane (`simple_web_layout_render_html_software_pixels` -> `paint()`) draws text
through `fb_text_ttf_aa_clip_range_adv` -> `_ttf_glyph_cached` -> `_ttf_rasterize_glyph`
(`simple_web_html_layout_renderer_paint_primitives.spl`, `..._paint_gradients_text.spl`).
That path never calls `sfnt_lcd_glyph_outline` / `_lcd_hint_knots`: its scale is
`font_size as f64 / units_per_em` with an `i32` size, so it has no y hinting and no milli size.
#10475 (fractional hint knots) therefore did not change it.

Ink rows (mean channel < 128), page `FF_PAGE` of
`test/01_unit/browser_engine/fractional_font_y_raster_chrome159_spec.spl`:

| band | size | Chrome | raster |
|---|---|---|---|
| 0 | 13.3333px mono | 2..11 | 3..11 |
| 3 | 21.3333px sans | 94..108 | 96..109 |
| 4 | 10.6667px sans | 132..139 | 133..139 |
| 6 | 16px sans (whole) | 172..183 | 173..183 |
| 1, 2, 5, 7, 8 | | match | match |

## Fix options
- (a) Route `_ttf_rasterize_glyph` through `sfnt_lcd_glyph_outline` (hinted knots + milli size) and take
  gray coverage from it. Changes whole-size raster output on purpose; re-check raster-lane specs.
- (b) Thread a milli size through `fb_text_ttf_aa_clip_range_adv` and callers. Only partial: band 6 stays off.

Neither the catalog nor the combo matrix runs the raster lane (they use cpu_simd and vulkan), so no ratchet row moves.
Recommended: (a), with an AC-3 `raster` row added to the spec above.
