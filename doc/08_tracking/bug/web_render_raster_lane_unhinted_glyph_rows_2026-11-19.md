# FIXED 2026-11-20 — raster backend: unhinted gray glyph rasterizer, ink rows off Chrome at whole and fractional sizes

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

## FIXED 2026-11-20 (option (a), gated at 48 px)

- `_ttf_rasterize_glyph` (`..._paint_gradients_text.spl`), for `font_size <= 48` without synthetic
  bold/italic, scans the commands of `sfnt_lcd_glyph_outline(blob, gid, size_px, size_milli)` (the
  hinted outline the cpu_simd / vulkan lanes draw) with its own exact-area gray rasterizer. Not the
  LCD raster's gray: that is FIR-blurred, so no 16 px stem reaches full coverage and
  `simple_web_window_renderer_spec` "realizes the declared solid fallback" (exact fg pixel) went red.
  48 px is Skia's `SK_MAX_SIZE_FOR_LCDTEXT` (`FONT_LCD_MAX_SIZE_PX` in `font_renderer.spl`); above it,
  and for synthetic styles, the plain-outline path stays byte-identical to base.
- `font_size_milli` is threaded through `fb_text_ttf_aa_clip_range_adv` -> `_ttf_glyph_cached` (key
  and hash carry it) -> `_ttf_rasterize_glyph`; the two raster callers pass `st.font_size_milli`.
- The text-run baseline is `ly + inline_line_strut_baseline_offset(st)`, the strut offset the Draw IR
  lanes use (face ascent/descent at the milli size, floored half-leading), not
  `fb_text_ttf_line_baseline_y` (whole-px ascent, rounded half-leading): 21.3333 px sat one row low.
- Trap (why the gate): an exact-area scan of the hinted 100 px outline inks a 1/4-px sliver above the
  stem-only cap tops (H, I, L) that are snapped 0.25 px above the E/F/T top bars, so H/I/L started one
  row above E/F/T (`web_pixel_font_capital_align_no_overlap_spec` went red). Chrome 159 at 100 px
  (gray text) keeps all seven tops on one row (36..104, B 36..105), and the 4-row LCD sampler hides it.
- Evidence: `fractional_font_y_raster_chrome159_spec` AC-3 (raster) red on base (bands 0, 3, 4, 6 as in
  the table above), green on head; AC-1/AC-2 unchanged.
- OPEN (not this fix, measured): with an explicit large `line-height` the raster lane draws the whole
  run lower than Chrome: `H E F I L T B` at 36 px / line-height 50 px has ink rows 15..40 vs Chrome
  11..36, at 100 px / 140 px 50..118 vs 36..104 (base identical in placement; cpu_simd matches Chrome).
