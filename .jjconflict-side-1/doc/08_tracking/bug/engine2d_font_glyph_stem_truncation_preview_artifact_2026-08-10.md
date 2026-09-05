# Engine2D vector-font "stem-truncated glyphs" — NO PIPELINE BUG; probe-viewing artifact

Date: 2026-08-10
Status: Closed — not a bug in the font pipeline. No source change made.

## Reported symptom

Text rendered through the engine2d FontRenderer vector TTF path (Noto Sans
Mono 12px) allegedly corrupted SPECIFIC glyphs into bare vertical stems:
'r' rendered like a stem, 'M' like 'I', 'O' of "Open" corrupt. Reported as
deterministic per character and identical on the cpu_simd and vulkan lanes,
with the staged atlas bitmap ASCII-verified correct — pointing the suspicion
at quad extraction (`font_atlas_subrect_pixels`), the blit
(`draw_image_blend`), dst computation, or the `GlyphCache`.

## Investigation (all runs: seed `src/compiler_rust/target/bootstrap/simple`,
interpreted — JIT falls back on these probes)

Probes (kept in /tmp on the investigation host; shapes reproducible from the
descriptions below):

1. `/tmp/blit_probe2.spl` — direct engine path
   (`Engine2D.create_with_backend(W,H,"cpu_simd")` + `select_font_identity` +
   per-char `draw_text_with_advances(x, 8, ch, [7], white, 12)`), dumping the
   staged quad, the atlas subrect, and the framebuffer cell after EVERY draw.
   Result: every quad correct, every atlas subrect correct, every framebuffer
   cell correct — for all 10 probe chars including 'r'.
2. `/tmp/blit_probe3.spl` — same but with `select_font_identity` before EVERY
   char (mimics the draw_ir handler). All correct.
3. `/tmp/blit_probe4.spl` — same, 10 chars, final-framebuffer dump. All
   correct; `font_execution_attempts` shows `vulkan:unavailable` →
   `cpu_simd:no-native-alpha-hit` → target `cpu`.
4. `/tmp/ir_n.spl` (N = 4, 5, 10) — the exact reported failing shape:
   `draw_ir_text_resolved_font` per char through
   `engine2d_draw_ir_adv_composition`. All correct.
5. `/tmp/alpha.spl` — full `A-Za-z0-9` as 62 per-char commands.
   `/tmp/alpha1.spl` — full alphabet as ONE command (advances [7]*62). Both
   numerically verified glyph-by-glyph against a FreeType (PIL) reference of
   the SAME TTF at 12px (`assets/fonts/google-fonts/ofl/notosansmono/
   NotoSansMono[wdth,wght].ttf`): best-translation IoU on binarized ink is in
   the normal unhinted-rasterizer band (~0.4–0.9) for EVERY glyph. 'M' shows
   both stems + diagonals; 'r' shows stem + top arm + bottom serif; no glyph
   is stem-truncated. Overlay dumps (`#`=both, `E`=engine-only, `r`=ref-only)
   confirm shape identity modulo 1px AA/hinting noise.
6. `/tmp/menubar.spl` — ["New","Open","Sync","Probe","Quit"] as 5 commands.
   'O' of Open is a full ring, 'r' of Probe has its arm; all IoUs in the
   normal band.
7. `/tmp/quad_probe2.spl` re-run — staged atlas bitmaps for N/O/r/o/w/M are
   all correct shapes, matching the framebuffer output pixel-for-shape.

Also verified: `vk_chars.spl` ("vulkan" everywhere) and its "cpu_simd"
variant produce BYTE-IDENTICAL ppm output (md5-equal) — on this host Vulkan
is unavailable (`vulkan:unavailable` in the execution attempts), so both
lanes genuinely execute the same CPU blit; the "identical on both backends"
observation carries no cross-backend information here. Output is also
deterministic across runs (identical md5 for repeat runs).

## Root cause of the OBSERVATION

The corruption was introduced at the VIEWING step, not in the pipeline.
The probes render 7x9px glyphs into a 320x60 (or wider) framebuffer; the ppm
was upscaled 4x with NEAREST to a 1280x240 png and then viewed through an
image-preview path that downsamples to fit (~300–1000px wide). At that
effective resolution the 1–2px features that distinguish 'r' from a stem
(the top arm) and 'M' from 'I' (the inner diagonals) are averaged away.
Every "corrupt" glyph cell, re-examined numerically from the same png/ppm
files, contains the correct full glyph. Simulation: downscaling the
numerically-verified-good alphabet render reproduces the "stem" appearance.

The staged-atlas ASCII dumps that "verified the atlas correct" were right —
and the framebuffer content matches those bitmaps exactly. The pipeline
(rasterize → GlyphCache → atlas stage → quad → subrect → blend) is correct
end-to-end on these probes.

## Regression sweep

- `test/01_unit/lib/common/ui/widget_draw_ir_glyph_run_spec.spl` — PASS (4/4).
- `test/01_unit/lib/common/text_layout/font_glyph_transparency_spec.spl` —
  PASS (3/3).
- `test/01_unit/lib/common/text_layout/font_renderer_spec.spl` — does not
  terminate on the interpreted seed: `daemon-worker-timeout` at the default
  ~120s daemon budget, and `child-timeout` even with a 900s direct
  `test_runner_single.spl` budget. Pre-existing/environmental (no source
  changes were made in this investigation; the spec drives the full browser
  font registry/download machinery — `ensure_browser_provided_fonts` et al. —
  interpreted, which does not finish in that budget on this host).
- `test/01_unit/lib/common/text_layout/font_identity_free_function_spec.spl`
  — PASS (1/1).
- `test/01_unit/lib/common/text_layout/font_render_config_spec.spl` — PASS
  (5/5) when run alone (an earlier concurrent attempt was OOM-killed on this
  7 GB host — an artifact of running several interpreted probes in parallel).

## Guidance

- Verify small-glyph rendering claims NUMERICALLY (per-pixel ASCII dumps or
  IoU against a reference raster at native resolution), never from a
  downscaled preview of an upscaled screenshot.
- If a genuine stem-truncation ever appears with numeric evidence, the
  suspects shortlisted by the investigation remain: `GlyphCache.lookup` /
  `lookup_index` key handling and `_font_atlas_entry_index` slot matching in
  `src/lib/nogc_sync_mut/text_layout/font_renderer.spl`, and
  `font_batch_apply_advances` dst rewriting in
  `src/lib/nogc_sync_mut/text_layout/font_advance_layout.spl`.
