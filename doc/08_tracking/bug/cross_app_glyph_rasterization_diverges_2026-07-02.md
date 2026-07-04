# Browser and GUI showcase use independently authored 5x7 glyph tables that diverge for most letters

Date: 2026-07-02
Status: fixed (2026-07-03) — shared 5x7 table; both paths byte-identical; advance unified at 5*scale
Severity: P2 (visual-parity gate, not a crash/data-loss bug)
Found by: W-G2.5 lane agent (source-verified, then confirmed with a rendered pixel oracle)

## Resolution (2026-07-03)

The browser side is pinned by checked-in exact-pixel baselines, so the browser
table is the source of truth. The fix:

- Extracted the browser's 5x7 table + lookups into ONE shared module,
  `src/lib/common/ui/glyph_bitmap_5x7.spl` (`FONT_ROWS_PACKED`,
  `FONT_UNKNOWN_PACKED`, `glyph_row_bits`, `glyph_index_for_char_code`,
  `glyph_index_for_char`, plus `glyph_rows_for_char` for Engine2D). The data is
  the browser's original array verbatim.
- `simple_web_html_layout_renderer.spl` now imports `glyph_row_bits` /
  `glyph_index_for_char_code` from the shared module (dead `FONT_CHARSET`,
  `_glyph_charset_index_of`, `glyph_index_for_char` removed).
- `std.gpu.engine2d.glyph.glyph_data()` delegates to
  `glyph_rows_for_char()`; the old `GLYPH_ROWS_PRINTABLE_ASCII` table and its
  helpers are deleted. Characters outside the shared 88-char charset now resolve
  to the shared box-outline unknown glyph (previously a solid block).
- Advance unified: Engine2D `glyph_advance(scale)` changed 6*scale -> 5*scale to
  match the browser paint advance (`text_advance = 5*glyph_scale`).

Verification (`scripts/check/check-cross-app-glyph-consistency.shs`): rendered
per-char oracle over `AEFHSVXYZ` = 0/1260 mismatched pixels; source-level
comparison over all 88 charset chars = 0 mismatched pixels, 0 mismatched chars;
`advance_engine2d=10 == advance_browser=10`; `glyph_consistency_status=identical`.
Browser exact-pixel baselines unchanged (html_compat, famous_site_corpus,
web_html_input, design_effects_compat specs all still pass).

### `char_w` left as-is (deliberate)

The task asked to also unify the browser's own internal wrap estimate
(`char_w(fs) = 6*glyph_scale`) with its paint advance (`text_advance =
5*glyph_scale`). `char_w` feeds line-wrap width estimates that set per-line
`x:` / `width:` in the checked-in exact-pixel html baselines; changing it moves
wrap points and dirties those baselines. Constraint 4 (browser pixels must not
move) overrides the char_w unification, so `char_w` stays `6*glyph_scale`. The
browser's internal wrap-vs-paint inconsistency therefore remains and is folded
into the stb_truetype convergence below.

### Residual (long-term convergence, no TODO)

Two items remain, both subsumed by the deferred stb_truetype migration:
(1) the browser's `char_w` wrap estimate (6*scale) vs paint advance (5*scale)
self-inconsistency, above; and (2) the integer scale formulas still differ
(Engine2D `font_size/7`, browser `font_size/8`) so cross-app identity is exact
at font-size 16 (both scale 2, the gate's size) but can diverge at other sizes.
Migrating both `draw_text` paths onto the shared `FontRenderer` /
`font_rasterizer.spl` (stb_truetype) stack closes both; until then the shared
5x7 table keeps the two paths byte-identical at the gated size.

## Summary

Gate G2.5 of `doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md`
asks that the browser and the GUI showcase "render shared UI chrome (buttons,
scrollbars, text) with identical glyph rasterization and theme tokens". They
do not. The two text-paint paths are backed by two separately hand-authored
5x7 bitmap fonts that agree on layout geometry (both use a 5x7 glyph cell and
`scale = font_size/8` rounded down) but disagree on which pixels are lit for
most letters, and additionally disagree on per-character advance.

## Evidence

- `scripts/check/check-cross-app-glyph-consistency.shs` +
  `src/app/test/cross_app_glyph_capture.spl` render the same characters via:
  - GUI showcase: `std.gpu.engine2d.backend_software.SoftwareBackend.draw_text()`,
    backed by `std.gpu.engine2d.glyph.glyph_data()`
    (`src/lib/gc_async_mut/gpu/engine2d/glyph.spl`, `GLYPH_ROWS_PRINTABLE_ASCII`).
  - Browser: the pure-Simple web layout renderer's text-paint path
    (`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`,
    `FONT_ROWS_PACKED` / `glyph_row_bits`).
  - Full source-level table comparison (both cover the same 88-character
    charset: A-Z, 0-9, space, punctuation, a-z): **41/88 characters
    byte-identical, 47/88 divergent**, including most uppercase letters
    (`B D E F H J S V X Y` and 26/26 lowercase letters — the browser table's
    lowercase glyphs are custom shapes, not an uppercase-fallback of the
    Engine2D table).
  - Rendered pixel oracle (per character, own canvas per app, so the
    unrelated advance-formula difference below cannot confound the glyph
    shape comparison) over `AEFHSVXYZ`: anchors `A` and `Z` render
    byte-identical (0 mismatched pixels each, 10x14px cell); the 7 characters
    in between (`E F H S V X Y`) each have 16-56 mismatched pixels out of 140
    per cell. Aggregate: 188/1260 mismatched pixels (85.1% pixel-match, but
    7/9 characters individually diverge).
  - Evidence PPMs: `build/cross-app-glyph-consistency/gui_glyphs.ppm`,
    `build/cross-app-glyph-consistency/browser_glyphs.ppm`.
  - `test/03_system/check/cross_app_glyph_consistency_spec.spl` asserts this
    current state (anchors match, the 7 middle characters diverge) so the
    gate stays honest until fixed — it does not assert "identical".

## Secondary finding: per-character advance also differs

Independent of glyph shape, the two engines' horizontal advance formulas
differ: Engine2D's `glyph_advance(scale)` in `glyph.spl` is `6 * scale`
(12px at scale 2), while the browser's `text_advance(fs)` in
`simple_web_html_layout_renderer.spl` is `5 * glyph_scale(fs)` (10px at
scale 2). A 9-character string with no spaces renders 106px wide in the GUI
showcase and 90px wide in the browser at the same font-size. (A third
value, `char_w(fs) = 6 * glyph_scale(fs)`, is used for the browser's own
line-wrap width estimate — it agrees with Engine2D's advance but not with
the browser's own paint-time advance, `text_advance`, which is a
self-consistency question worth checking too.)

## Impact

Any pixel-level golden-image comparison across the two apps (or against a
shared design reference) will show text mismatches purely from the glyph
tables and spacing, independent of layout/theme-token correctness. Gate
G2.5 cannot be marked done until one of the two paths adopts the other's
glyph table (or both adopt a shared one, e.g. the stb_truetype font stack
already used elsewhere per `src/lib/nogc_sync_mut/text_layout/font_rasterizer.spl`).

## Suggested fix

Point one of the two `draw_text` implementations at the other's glyph table
(or extract a single shared 5x7 table + shared advance formula used by both
`std.gpu.engine2d.glyph` and `simple_web_html_layout_renderer.spl`'s
`glyph_row_bits`/`text_advance`). Not attempted here — capture+detection lane.

### Regression constraint (verified during G2.5 review — why this is NOT a small diff)

Neither table can be swapped unilaterally as a contained change:

- **Browser side is pinned to exact-pixel baselines.** `FONT_ROWS_PACKED` is the
  paint-time glyph table for the general `simple_web_render_html_to_pixels`
  path (via `fb_text_*` in `simple_web_html_layout_renderer.spl`). That path
  feeds checked-in exact-pixel browser baselines
  (`test/09_baselines/html_compat/*`, `web_html_input/*`, `design_effects_compat/*`).
  Changing 47 glyph shapes would dirty all of them. The famous-site corpus
  (G2.2) is partially insulated — it composites Chrome-calibrated LCD ink from
  `test/09_baselines/famous_site_corpus/glyph_atlas/arial16_lcd_v1.bin` over the
  base render and "fails closed to block-only rendering" for uncalibrated
  samples — but its acceptance policy is `exact_required: true`
  (`tolerance_acceptance_allowed: false`) and its signature includes per-line
  `x:` / `width:`, which the browser's `text_advance = 5*glyph_scale` sets. So
  changing the **advance** formula browser-side is also unsafe.
- **Engine2D side would dirty GUI baselines** and requires the advance change to
  land in `glyph_advance` (`6*scale`), affecting the GUI showcase render
  (owned by a separate lane — `examples/06_io/ui/widget_showcase_gui.spl`,
  `gui_low_res_readability`).

Correct (larger) fix, deferred: migrate BOTH `draw_text` paths onto the shared
`FontRenderer`/`src/lib/nogc_sync_mut/text_layout/font_rasterizer.spl`
(stb_truetype) stack that `glyph.spl`'s own header already claims to converge
on, then regenerate every affected browser + GUI baseline atomically in one
change. The advance formulas must be unified in the same change (Engine2D
`6*scale`, browser paint `5*scale`, browser wrap-estimate `char_w = 6*scale` —
three values, currently self-inconsistent even within the browser). Until then
the two 5x7 tables stay divergent by design and this gate stays honestly open.
