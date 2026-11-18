# Glyph advances come back as whole pixels once a page uses more than 8 (face, size) pairs

- **Status:** open, not fixed. Found by the LCD raster perf lane (2026-11-19), which had to reproduce it to keep its output byte-identical.
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
