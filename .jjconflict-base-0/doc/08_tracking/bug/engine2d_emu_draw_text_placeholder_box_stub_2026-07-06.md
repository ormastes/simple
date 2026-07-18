# emu_draw_text / emu_draw_text_bg are placeholder box STUBS, not real text

## Status
Fixed (2026-07-06).

## Severity
High — fake rendering. The stateless emulation layer that gives Core-only
backends their advanced-op coverage produced a generic box for EVERY glyph,
so any backend routed through `emu_draw_text*` rendered unreadable placeholder
rectangles instead of text.

## Summary
`emu_draw_text` (`src/lib/gc_async_mut/gpu/engine2d/backend_emu.spl:276`) and
`emu_draw_text_bg` (`:302`) stamped a fixed box (3 horizontal bars + 2 vertical
bars) IDENTICALLY for every non-space character, ignoring glyph identity
entirely — a fake. The real rendering path is `SoftwareBackend.draw_text`
(5x7 `glyph_data` bitmap blit) and `SoftwareBackend.draw_text_bg`
(anti-aliased `text_aa_blit_buffer` composited via `draw_image`).

Both emu functions receive `mut core: RenderBackend`, and `draw_text` is a
`RenderBackend` trait method — so the emu layer can and should delegate to the
real backend instead of faking glyphs.

## Evidence
Measured on the shared-raster parity harness (48x48 surface, string `"Hi"`,
font_size 8):

| Op | sw non-bg px | emu non-bg px | mismatch |
|----|-------------|---------------|----------|
| `draw_text`    | 25 (real `Hi` glyphs) | 40 (identical boxes) | 33 |
| `draw_text_bg` | 80 (AA blit)          | 70 (bg + boxes)      | 43 |

The box stub paints MORE ink (40) than the real two-letter word (25), and is
byte-identical regardless of which characters are passed.

## Fix
- `emu_draw_text` now delegates to `core.draw_text(x, y, text_val, color,
  font_size)` — the real 5x7 glyph blit. Byte-identical to
  `SoftwareBackend.draw_text`.
- `emu_draw_text_bg` now delegates to the real anti-aliased text-on-background
  blit via `text_aa_blit_buffer(...)` + `core.draw_image(...)`, matching
  `SoftwareBackend.draw_text_bg` byte-for-byte. NOTE: the naive composition
  "`core.draw_rect_filled(bg)` + `core.draw_text(fg)`" does NOT reach
  byte-exactness, because `SoftwareBackend.draw_text_bg` uses the AA blit
  (`text_aa_blit_buffer`), whose payload height is `max(font_size, glyph_px)`
  and whose edge pixels are coverage-blended — a hard bg-rect + non-AA glyph
  composition diverges from it (empirically stays non-zero). The harness names
  `[canonical: sw]` for `draw_text_bg`, so the emu layer matches the sw AA path.

## Verification
`test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl`:
`cmp_text()` and `cmp_text_bg()` now return 0 (were 33 and 43). Both harness
assertions were flipped from `> 0` (pinned divergence) to `== 0` (byte-exact)
and stay green.
