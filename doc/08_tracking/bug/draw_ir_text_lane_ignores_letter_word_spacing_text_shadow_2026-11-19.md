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

## Update 2026-11-19: letter-spacing and word-spacing resolved; text-shadow still open

The composer (`_html_draw_ir_resolved_text_command`) now folds `letter-spacing` (every codepoint) and `word-spacing` (each U+0020) into the command's `advance_widths` and width, the same fold layout already did, and both are dropped from `_simple_web_engine2d_raster_only_text_property` (only `text-shadow` stays). Also fixed: `-1px` was read as `+1` (`parse_int` drops the sign) and `0.1em` as 0; both now parse (`_decl_signed_spacing_px`). Pinned by `drawir_letter_word_spacing_chrome159_spec` (Chrome 159 measured).

Fractional spacing resolved (same day): `Style.letter_spacing_milli`/`word_spacing_milli` carry the exact value; layout and Draw IR fold it at rounded cumulative pens and the exact spacing reaches the glyph pen phases (`letter-spacing-milli` / `word-spacing-milli` props). `0.1em` ink x1 163 and `-1px` 126 now match Chrome. Still open: a shaped run (`shaping_required`) does not carry the spacing in its glyph_run; text-shadow is unchanged.

## Update 2026-11-19: shaped (Arabic) runs

The shaped lane (Arabic with `lang="ar"` -> Noto Sans Arabic, `glyph_run.valid`) took the same per-codepoint fold, so layout widened an Arabic run by one gap per letter. Chrome 159 adds letter-spacing to every unit except Arabic-script letters (joined or isolated): `مرحبا بالعالم` 77.09 -> 79.09 at 2px (the one space), `م ر ح` +4, `مرحبا abc` +8; word-spacing adds to each space. `spaced_advances_milli` now skips the letter gap for `Script.Arabic` codepoints; the Engine2D paint follows the command advances, so no glyph-run change was needed. Pinned by `shaped_run_spacing_chrome159_spec.spl` (4 of 6 red on base, 6 green after). Ligatures: no Latin run takes the shaped path (only Arabic/Devanagari do), so Chrome's "no optional ligatures when spaced" has no case to pin here.

Still open: Devanagari (`lang="hi"`) never gets a valid glyph run (`glyph_run.valid == false`, per-codepoint fallback, `नमस्ते दुनिया` width 103 vs Chrome 72.91), so Chrome's per-grapheme-cluster spacing (+16 at 2px, 8 clusters) cannot be matched until Devanagari shaping works. Mixed-direction runs (`مرحبا abc`) are only pinned for layout width, not for pen positions.
## Update 2026-11-19: sharp text-shadow resolved; blur still open

Offset shadows with blur 0, including several comma-separated layers (first listed on top), are painted by the Draw IR text lane as one extra text command per layer under the run (`_html_draw_ir_text_shadow_commands`). Pinned against Chrome 159 by `drawir_text_shadow_chrome159_spec` (bbox, shadow-colour pixel counts, LCD fringe). Not done: `text-shadow` with blur > 0 (Chrome paints a grayscale Gaussian halo, e.g. `0 0 3px black` ink bbox 18,29-168,49). Engine2D has box-shadow blur but no glyph-mask blur, so `_simple_web_engine2d_raster_only_text_property` still keeps a blurred bare-text page on the raster lane, and the raster lane does not paint the blur either. A `<p>` page with a blurred shadow takes Draw IR and paints no shadow. Cost note: moving a shadowed bare-text page from the raster lane to Draw IR takes a cold `simple run` render from 1.95 s to ~3.9 s, which is what any Draw IR page costs (plain page 3.8-4.0 s); RSS unchanged (~740 MB).

## Update 2026-11-19: Devanagari root cause (no shaper beyond one pinned word)

Why `glyph_run.valid == false` for Devanagari: the canonical OpenType lane admits exactly ONE Hindi string. `resolve_canonical_layout_run` (`src/lib/skia/feature/shaper/ot_layout_shaper.spl:222`) returns `None` unless `_selected_text` (`ot_layout_shaper.spl:64-80`) accepts the run, and for `dev2` that is only `language == "hi"` and the six codepoints U+0939 U+093F U+0928 U+094D U+0926 U+0940 (`हिन्दी`). `_nominal` (`:174-185`) hardcodes that word's reorder/cluster table, and `selected_devanagari_glyphs` (`selected_devanagari.spl:165`, "deliberately one pinned dev2 witness, not general Indic shaping") only matches the same word. For any other text `canonical` is `None`, so `_build_run` (`shaper.spl:704-709`) sets `substitution_complete`/`positioning_complete` false and `shaped_run_to_font_glyph_run` (`shaper.spl:741`) marks the run invalid; the glyphs come from the minimal fallback `_shape_devanagari_run` (`shaper.spl:457`, reph only, no GSUB features). Font mapping and admission are fine: `lang="hi"` selects bundled Noto Sans Devanagari (`font_registry.spl:700,713`), the face is in `assets/fonts/google-fonts/ofl/notosansdevanagari/`, and the pinned word itself yields `valid=true`.

Measured 2026-11-19 (probe through `simple_web_layout_render_html_draw_ir`, `lang="hi"`, 16px): `नमस्ते दुनिया` 103 valid=false (13 glyphs, one per codepoint), `कमल` 33 false, `क्ष` 28 false, `स्ते` 33 false, `हिन्दी` 30 true. Chrome 159 with the same bundled face via `@font-face` (Range.getBoundingClientRect): 72.91, 32.72, 11.48, 15.36, 30.23. Without the `@font-face`, Chrome has no Noto Sans Devanagari here (`fc-match` answers DejaVu Sans) and falls back to a system face: 76.17, 32.11, 10.27, 17.67, 31.16, so use the `@font-face` numbers as the oracle. Even non-conjunct `कमल` is invalid because the gate is text-based, not shaping-based.

Not fixed: this needs real Indic shaping (syllable segmentation, reph, pre-base matra reordering, half forms/conjunct GSUB lookups with the context lookups the font uses, mark positioning, cluster-based advances), generalising the pinned-witness code in `ot_layout_shaper.spl` and `selected_devanagari.spl`. Estimate: a general `dev2` shaper is roughly 1-2 kLOC of Simple plus Chrome-oracle specs per script class, several days of work; not a small admission-guard fix. Per-cluster letter-spacing for Devanagari stays blocked on it.

## Update 2026-11-19: blurred text-shadow on Draw IR is blocked on a missing primitive (inventory)

What exists in Engine2D: `draw_shadow_rect` (rect box-shadow, `shaders/shadow_rect.comp`, `draw_ir_box_effects.spl`) and `draw_blur_rect` (`backend_emu_adv.spl:137` `emu_draw_blur_rect`, twin `shaders/blur_rect.comp`), a separable integer BOX blur that reads the current framebuffer region and writes it back, used for `backdrop-filter`. What is missing: (1) any per-element `filter: blur()` or offscreen/save-layer for arbitrary commands (`css_opacity_group.spl` is opacity compositing only, no blur); (2) a glyph-coverage mask extraction, so a blurred copy of text cannot be rendered into an isolated layer; (3) a Gaussian kernel (box blur is not Chrome's Skia sigma = radius/2 Gaussian) and a tint-by-shadow-colour composite under the text. `draw_blur_rect` blurs the framebuffer in place (it would blur whatever is already painted, including the page background and earlier text), so it cannot stand in for a shadow mask. Wiring blur into `_html_draw_ir_text_shadow_commands` therefore needs a new offscreen-layer + Gaussian + tint primitive across CPU/emu/Vulkan backends, well above a small diff; not built. The routing hold in `_simple_web_engine2d_raster_only_text_property` stays.
