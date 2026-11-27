# Glyph advances come back as whole pixels once a page uses more than 8 (face, size) pairs

- **Status:** RESOLVED 2026-11-19 (see "Resolution" below). Found by the LCD raster perf lane (2026-11-19), which had to reproduce it to keep its output byte-identical.
- **Where:** `FontRenderer.get_glyph_advance_milli`, `src/lib/nogc_sync_mut/text_layout/font_renderer.spl`.

## What happens

The milli-pixel advance cache has 8 ASCII slots, one per (face identity, size), evicted round-robin (`_ADV_ASCII_SLOTS`, `_adv_cache_store`). On a slot miss `get_glyph_advance_milli` first asks the renderer's own `GlyphCache`:

```
if val Some(cached_adv) = cached:
    val _cached_milli = cached_adv.advance * 1000
    _adv_cache_store(_adv_identity, font_size, codepoint, _cached_milli)
    return _cached_milli
```

A rasterised glyph only carries a whole-pixel advance. So a glyph that was drawn before its slot was evicted answers `round(advance) * 1000` from then on, and the refilled slot keeps that value. The real milli advance (`meta[18]` of the index lane below) is only read for glyphs that were never drawn.

The result depends on the order of measuring and drawing, not on the text.

## Reproduction

A page with four faces (regular, bold, italic, bold italic) and sizes 1, 2, 3 and 4 px, one line each of `Hamburgefonstiv Qy,.:;19` (16 pairs; the lane's `u14x4` page). With a trace in `_lcd_apply_pen_phases`:

- the glyphs of the first 4 px run are kept on their phase-0 cells (`phase = 0`), because the pens built from the refilled advances are whole pixels;
- the same glyphs get quarter phases 1 to 3 when the glyph cache holds no entry for those glyphs at the time of the refill (the lane's first draft, which did not put deferred cells into the glyph cache);
- the two renders differ on the 1 px and 4 px lines. The same page with one face (4 pairs) or one size (4 pairs) renders the same either way.

Sizes 1 to 15 in four faces differ on the 1, 4, 8, 12 and 15 px lines by the same mechanism.

## Not measured

Which of the two renders is closer to Chrome. The layout's own advances go through the same function, so the fix moves both the pens and the layout widths.

## Fix direction

Drop the glyph-cache branch for the selected-outline backend (the index lane below it answers the milli advance from `hmtx` without a raster), or store the milli advance on the cached glyph. Either changes pixels on any page with more than 8 (face, size) pairs, so it needs a Chrome-measured spec and a catalog pass.

## Resolution (2026-11-19)

`get_glyph_advance_milli` no longer answers from the glyph cache when the face has a selected outline blob. The index lane and the direct lane read the exact `hmtx` milli advance (`meta[18]`) without a raster, so a refilled slot holds the same value as a first fill. The cached whole pixel is kept only as the fallback for a glyph neither blob lane can answer, and as the direct answer on backends with no blob (unchanged there).

Which render is closer to Chrome, the open question above: the exact one.

- Chrome 159 `getBoundingClientRect().width` of `H` at 13 px in Liberation Sans is 9.390625 px. After an eviction and a draw the function answered 9000 milli; now 9388.
- Twelve sizes (12 to 23 px) of `Hamburgefonstiv Qy,.:;19` in one face, 520x340, pixels with a channel more than 8 from Chrome / summed |delta|: 13272 / 1,585,925 before, 5506 / 479,830 after. No line is worse; the 18 px line is unchanged (458 / 42,854).
- Catalog `html` at 1x: 2.35 % to 1.78 %.

Spec: `test/01_unit/browser_engine/glyph_advance_eviction_exact_chrome159_spec.spl`.

Cost (cpu_simd, interpreter lane, same seed, wall / peak RSS): the twelve-size page is unchanged (16.1 and 17.0 s / 670 MB before, 15.9 and 13.6 s / 674 MB after). A page of 36 paragraphs in nine faces at one size went from 32.1 s / 758 MB to 36.7 s / 729 MB: its glyphs now take the quarter-phase LCD cells that a page with 8 pairs or fewer always took. The dpr4 catalog is unchanged on every page.
