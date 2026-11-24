# Shaped Devanagari runs at device scale 4 miss Chrome's ink (2026-11-23)

**Status:** open. **Red spec:** `test/01_unit/browser_engine/devanagari_render_k4_chrome159_spec.spl`
(`@tag:in-development`, Chrome 159 k=4 ink boxes for the ten render-table words).

At 1x the glyph runs (ids, pen x, mark y) and the right/bottom ink edges of
these words equal Chrome's. At k=4 (384 dpi) three separate defects show.
Measured on the GSUB lane head (general dev2 shaper) plus this lane, cpu lane;
the k=4 Chrome capture was validated by reproducing the 1x table at factor 1.

## 1. Pen x snapped in CSS px, then scaled (owner: shaped-run payload + `draw_ir_device_scale`)
`shaped_run_to_font_glyph_run` (`src/lib/skia/feature/shaper/shaper.spl`)
stores `xs` as whole CSS px; `draw_ir_device_scale.spl` multiplies them by k.
Device pen = 4*floor(p) where Chrome uses floor(4p):

| word | glyph pen px | Simple 4*floor | Chrome floor(4p) | x1 Simple / Chrome |
|------|--------------|----------------|------------------|--------------------|
| ड़ुँ  | 101 @ 8.768  | 32 | 35 | 114 / 117 |
| द्धू  | 35 @ 13.552  | 52 | 54 | 140 / 142 |
| नहीं  | 635 @ 17.376 | 68 | 69 | 165 / 166 |
| कुछ  | 62 @ 12.288  | 48 | 49 | 173 / 174 |

The Latin control `Hxgl` (unshaped path) is also 2 device px short on x1
(201 vs 203), so the class is not Devanagari-only.
Design: carry the fractional pen (26.6, `position.x * 64`) beside `xs` in
`DrawIrGlyphRunPayload` and let `draw_ir_device_scale` compute
`floor(x64 * k / 64)` (y: round). At k=1 that equals the current
truncate-x / round-y rule byte for byte, so 1x output cannot move. It touches
the shared Draw IR payload (SDN writer, paint-chunk snapshot, metal/vulkan
consumers), so it is a cross-backend change. Chrome also positions glyphs at
sub-pixel x at 1x (नहीं / कर्म 1x x1 41 vs 42); that needs sub-pixel glyph raster,
a separate step.

## 2. Shaped-run baseline 1 device px high (owner: font_renderer selected-run stager)
Every shaped word's top ink row is 1-2 device px above Chrome's at k=4 and
its bottom row 1 above on eight of ten words (हिन्दी 120..186 vs 121..187;
कुछ and टुँ keep Chrome's bottom row 195), while the Latin control's rows are equal
(132..192 both). Suspected (not verified): `_stage_selected_glyph_run_active`
(`src/lib/nogc_sync_mut/text_layout/font_renderer.spl`) takes its baseline from
the run face's ascent measured at k x font-size (`sfnt_measure_glyph_into`
meta[17]); the unshaped path places the baseline from the line metrics.
Not yet located which rounding differs.

## 3. Empty buffer when a command is skipped at k=4 (owner: web device-scale path)
`simple_web_layout_render_html_pixels_engine2d_at_device_scale`
(`simple_web_layout_engine2d_fast.spl`) returns `[]` when
`skipped_command_count != 0`. A shaped Devanagari command the stager declines
(हिंदी: glyph 785 is empty, so `glyph.width <= 0` invalidates the run; before
the general dev2 shaper every word but हिन्दी) therefore yields no frame at
k=4, while 1x paints the per-codepoint fallback.

## Status 2026-11-24 (branch work/webrender-intl4x-20261124)

- **Defect 1 fixed.** Resolve keeps each glyph's pen in 1/64 px
  (`glyph_pens_64`). Paint (`simple_web_html_layout_renderer_paint_draw_ir.spl`)
  emits `device-glyph-xs` = floor(k x pen), and `draw_ir_device_scale` swaps it
  in for `k x glyph_run.xs`. There is no payload change.
  All ten words' ink x now equal Chrome's (base: 7 of 10 off).
- **Defect 3 fixed, and it was wider than Devanagari.** The stager now skips an
  outline-less glyph (`_selected_glyph_is_blank`: a clean measure with no
  coverage) instead of declining the run. That also covers the Arabic space, so
  every multi-word `lang="ar"` run used to blank the whole k=4 frame. A run the
  Arabic shaper declines (`مرحبا123`, `مرحبا.`) now paints per codepoint instead
  of being sent as an invalid shaped command. Corpus pages 33-bidi and
  48-overflow-ellipsis paint at k=4 (base: no frame).
- **Defect 2 is open. Owner: layout (`device_dy`), not the stager.** The stager
  places the baseline at command y + the shaped face's ascent at k x size, and
  command y = 4 x 30 + device_dy. Layout's device_dy is +1 here: the strut's
  half-leading.

  | text | Simple baseline | Chrome baseline |
  |------|-----------------|-----------------|
  | Devanagari | 121 + 57 = 178 | 179 (44.75 CSS) |
  | Arabic, Noto only | 121 + 88 = 209 | 208 = 120 + 88 |

  For Devanagari the Liberation strut's ascent (58) dominates the line; for
  Arabic the face's ascent dominates, so the +1 must not apply. That is a
  line-box (strut vs. run ascent) rule, which belongs to the layout lane.
