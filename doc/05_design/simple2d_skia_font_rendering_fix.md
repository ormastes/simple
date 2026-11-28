# Design: Unified Subpixel Font Positioning & Skia/Simple2D/Browser Parity Fix

**Goal:** Eliminate mid-word splits/overlaps (`"Mod ule"`, `"flo ated"`), right-edge label/badge collisions (`"HTML/CSS Render Parity"` vs `"Forms & Paint"`), and Skia vs Simple2D font metric/placement discrepancies while preserving existing Chrome 159, Vulkan bitmap-atlas (`G2.5`), and Skia unit contracts.

---

## 1. Shared Architectural Strategy (Zero Duplicated Math)

Instead of letting SFNT, `text_layout`, `engine2d`, `skia`, and `browser_engine` maintain independent integer rounding and ad-hoc scaling logic, establish one coherent progression:

1. **Common Encoding (`src/lib/common/encoding/sfnt_kern.spl`, `sfnt_glyf.spl`):**
   - `sfnt_kern_face_pair_size_milli_px(blob, face_info, left_gid, right_gid, size_milli)` scales `kern` in exact milli-px for both integer (`size_px * 1000`) and fractional (`font_size_milli`, e.g., `13333`, `18720`) CSS sizes using symmetric round-half-away-from-zero. `sfnt_kern_face_pair_milli_px` delegates directly to it.
   - `sfnt_glyf_measure_codepoint_advances_kerned(blob, codepoints, size_px, apply_kern)` shares `sfnt_glyf_measure_codepoint_advances` `hmtx` reading and adds `sfnt_kern_face_pair_size_milli_px / 1000.0` to each preceding glyph when `apply_kern == true`.
   - `sfnt_subpixel_pen_split_milli(pen_milli)` maps continuous `pen_milli` (relative to integer base pixel) into `(whole_px, phase_q)` with Chrome/Skia quarter-pixel phase snapping (`(pen_milli + 125) / 250` floor-aligned), guaranteeing one canonical `phase_q in 0..3` formula across `FontRenderer` and Browser TTF painting.
   - `sfnt_measure_glyph_into` preserves `meta[3] = _round_glyf_metric(hmtx.lsb * scale)` for existing `spl_fonts` / `native_glyph_contract` callers, and writes `meta[19] = _floor_glyf_px(bounds.left * scale)` (contour `xMin` origin matching `_outline_edges` at `sfnt_glyf.spl:1087`) so unphased gray glyph blitters align with the rasterized contour's true left side bearing when `lsb != xMin`.

2. **Text Layout (`src/lib/nogc_sync_mut/text_layout/font_renderer.spl`, `font_advance_layout.spl`, `font_rasterizer.spl`):**
   - Fix `FontRenderer.horizontal_kern` (`2343`) / `horizontal_kern_milli` (`2382`): add `horizontal_kern_size_milli(left_cp, right_cp, font_size_milli)` using `sfnt_kern_face_pair_size_milli_px` so fractional sizes kern accurately too.
   - Fix `FontRenderer.render_text` (`3212`) & `render_text_payload` fallback (`3241`): replace per-glyph integer `cx = cx + glyph.advance` and integer `horizontal_kern` with cumulative milli-px pen stepping (`measure_text_advances` / cumulative milli boundaries + `horizontal_kern_milli`) and apply vector `bearing_x` / `bearing_y` placement when `not self.use_bitmap` (preserving top-left cell placement when `self.use_bitmap` is true for `font_renderer_placement_spec.spl`).
   - Fix `FontRenderer._resolve_selected_shaped_glyph_run` (`4504-4515`): accumulate `total_advance` in `f64` and compute `before`, `after`, and final `width` using nearest-pixel rounding `(x + 0.5).floor().to_i32()` instead of `.to_i32()` truncation.
   - Align `FontRenderer` unphased gray glyph `bearing_x` using `meta[19]` (`bounds.left * scale`) when available (`lsb != xMin` consistency with `_outline_edges` and Skia's `sfnt_rasterize_glyph_baseline_aligned`).
   - Keep `_lcd_apply_pen_phases` and `resolve_font_metrics_with_language_milli` quarter-phase / 26.6 cache-key invariants intact.

3. **Engine2D (`src/lib/gc_async_mut/gpu/engine2d/glyph.spl`, `font_owner.spl`, `backend_software.spl`, `backend_cpu.spl`):**
   - Preserve `glyph_advance(scale) = 5 * scale` for Vulkan dense 5xN bitmap atlas tiling (`backend_vulkan_font.spl:910`) and G2.5 (`cross_app_glyph_consistency_spec.spl`).
   - Add `glyph_spaced_advance(scale) = 6 * scale` (`5 * scale + 1 * scale` inter-glyph gap matching `skia_bitmap_5x7_metrics` / `ascii_glyph_advance_x`) and `render_text_spaced_to_buffer(...)` + `draw_text_spaced(...)` on `SoftwareBackend` / `CpuBackend` so Engine2D has a zero-overlap 5x7 text lane matching Skia bitmap fallback.
   - Fix UTF-8 codepoint iteration in `glyph.spl:157` (`render_text_to_buffer`) and `backend_software.spl:733` (`SoftwareBackend.draw_text`) using `text_codepoints(text_val)` instead of `text_val.len()` (byte length).
   - Expose Skia-parity SFNT measurement/kerning helpers on `Engine2DFontOwner` (`engine2d_font_owner_measure_advances_milli`, `engine2d_font_owner_run_width_px`) backed by `FontRenderer.measure_text_advances` / `horizontal_kern_milli`.

4. **Skia (`src/lib/skia/entity/font.spl`, `feature/glyph/font_metrics.spl`, `feature/glyph/rasterize.spl`, `feature/shaper/shaper.spl`):**
   - In `font.spl`: add `sk_font_measure_codepoints_advances_kerned(font, cps, apply_kern, allow_default_fallback)` reusing `sfnt_glyf_measure_codepoint_advances_kerned` so Skia exposes kerning-aware advances matching `FontRenderer` while keeping existing callers unchanged.
   - In `font_metrics.spl`: add `font_metrics_line_box_units(data: [u8])` (`OS/2` typo metrics when `fsSelection & 0x80 != 0` else `hhea`, matching Chrome & `sfnt_blob_line_metric_units`) and `font_metrics_scale_px(units, size_milli, upem)`.
   - In `rasterize.spl`: add `rasterize_outline_with_upem(outline, size_px, units_per_em)` using `scale = size_px / units_per_em` when `units_per_em > 0`, while `rasterize_outline` delegates with `units_per_em = 0` (`max(em_w, em_h)` fallback preserved for `glyph_spec.spl`).
   - In `shaper.spl`: preserve `shaped_run_to_font_glyph_run`'s pinned `xs` truncation + `ys` rounding contract (`shaped_run_glyph_y_round_chrome159_spec.spl`), and add `shaped_run_rounded_advances(run)` / `shaped_run_total_advance_px(run)` using nearest-pixel rounding of cumulative `f64` advances without truncation drift.

5. **Browser Engine TTF Rasterizer (`paint_gradients_text.spl` + `paint_raster.spl`):**
   - Strictly respect file ownership: keep `simple_web_html_layout_renderer_paint_primitives.spl` untouched and stay under `128 KiB` in `paint_gradients_text.spl`.
   - In `paint_gradients_text.spl`:
     - Add `_ttf_effective_milli(font_size, font_size_milli)` using `sfnt_font_cache_key_size_26_6(raw_milli)` -> `keyed_milli` so ALL paths (regular `<= 48px`, `> 48px`, `synth_bold`, `synth_italic`, baseline/ascent, and advance stepping) agree on the exact Chrome 26.6 fractional size (`18.715` == `18.718` == `18.72` invariant preserved!).
     - Share `_ttf_rasterize_glyph_phased(face, gid, font_size, font_size_milli, synth_bold, synth_italic, phase_q)` between `_ttf_rasterize_glyph` (`phase_q = 0`) and our new cached phased glyph lookup `_ttf_subpixel_glyph_cached(..., phase_q)`. Apply `phase = (phase_q as f64) * 0.25` horizontally before `min_x`/`max_x` flooring/ceiling (`x0_px = _ttf_floor_i32(min_x + phase)`, `ox = (x0_px as f64) - phase`), matching Skia `sfnt_rasterize_glyph_baseline_aligned` and `sfnt_lcd_outline_frame`!
     - Fix `_ttf_hmtx_advance_px` (and add `_ttf_hmtx_advance_milli(face, gid, eff_milli)`) using `eff_milli / (1000 * upem)` instead of integer `font_size`.
     - Add `ttf_ascent_px_milli`, `ttf_line_baseline_y_milli`, and `ttf_paint_text_aa_clip_range_adv` in `paint_gradients_text.spl`:
       - When `use_by` is true (`by.len() == s_blen`), anchor integer pen boundaries to layout's `by` prefix sum while reconstructing true milli-px pen positions (`hmtx_milli + kern_milli`) between glyphs (clamped/aligned to `by` boundaries just like `FontRenderer._lcd_apply_pen_phases`) so each glyph renders at its true quarter-pixel `phase_q` (`base_x + phase_q * 0.25`), preventing `"Mod ule"` / `"flo ated"` rounding-oscillation splits.
       - When `use_by` is false (e.g., `text_overflow_ellipsis`), accumulate continuous milli-px `pen_milli` (`hmtx_milli + kern_milli + synth_bold_advance_milli`) with `phase_q` extraction, preventing multi-pixel drift and bold self-overlap.
       - Ensure synthetic bold (`bold_extra`) when `use_by` is true clips/clamps excessive inter-glyph bleed or widens fallback advance cleanly when `use_by` is false so right edges never overrun boxes.
   - In `paint_raster.spl` (strictly TTF text stepping & raster placement lines `12-18`, `1788-1895`):
     - Import `ttf_paint_text_aa_clip_range_adv`, `ttf_ascent_px_milli`, `ttf_line_baseline_y_milli` from `paint_gradients_text.spl`.
     - Remove the spurious `+ text_ink_x_offset(st.font_size)` (`+1 px`) when `use_ttf == true` (`val text_x = if use_ttf: x else: (x + text_ink_x_offset(st.font_size))`), matching Draw IR and `<input>` TTF placement.
     - Route both `<input>` and `#text` TTF text painting through `ttf_paint_text_aa_clip_range_adv` and `ttf_ascent_px_milli` / `ttf_line_baseline_y_milli`.

---

## 2. Verification & Spec Plan

- **Unit Spec:** `test/01_unit/lib/nogc_sync_mut/text_layout/simple2d_skia_font_parity_spec.spl`:
  - Fractional `font_size_milli` (`13333` / `13.333px` and `18720` / `18.72px` vs `18715`) scaling, advance accumulation, and quarter-phase `phase_q` partitioning.
  - Kerning pairs (`"AV"`, `"To"`, `"Mo"`, `"fl"`) with `sfnt_kern_face_pair_size_milli_px` and `FontRenderer.horizontal_kern_milli` / `horizontal_kern_size_milli`.
  - `lsb != xMin` bearing alignment (`meta[19]` vs `_outline_edges` `bounds.left` parity).
  - Synthetic bold advance & non-overlapping bitmap bounds (`bold_extra` without adjacent ink collision on fallback stepping).
  - Engine2D 5x7 spaced advance (`6 * scale`) parity with Skia 5x7 fallback (`<= 1px` width diff, `0` horizontal ink overlap) and UTF-8 codepoint stepping.
  - Skia `sk_font_measure_codepoints_advances_kerned`, `font_metrics_line_box_units`, `rasterize_outline_with_upem`, and `shaped_run_rounded_advances` parity against `FontRenderer`.
- **Static & Isolated Seed Checks:**
  - `sh scripts/audit/direct-env-runtime-guard.shs --working` & `--staged`.
  - `find doc/06_spec -name '*_spec.spl' | wc -l` == `0`.
  - `wc -c` check keeping `paint_gradients_text.spl < 131072` bytes.
  - Nov 16 seed (`--memory-limit=1G`, `SIMPLE_LIB=/tmp`) isolated syntax/parse check on every modified/added `.spl` file + standalone numeric verification probe in `/tmp`.
