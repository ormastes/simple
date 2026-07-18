<!-- codex-research -->
# Simple 2D Vector Fonts — Local Research

Date: 2026-07-11

## Finding

Vector-font support exists below Simple 2D but was never connected to its public drawing facade. This is integration and hardening work, not recovery of deleted code.

## Existing Paths

- `src/lib/gc_async_mut/gpu/engine2d/engine.spl:628-635` documents `Engine2D.draw_text` as bitmap-only and delegates to backend implementations.
- `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl:354-406` renders the shared packed 5x7 atlas directly; GPU and bare-metal siblings use the same bitmap model.
- `src/lib/nogc_sync_mut/text_layout/font_renderer.spl:17-249` already selects TTF, built-in vector outlines, then bitmap fallback and owns caching, measurement, kerning, and ARGB blitting.
- `src/lib/nogc_sync_mut/text_layout/font_vector_data.spl:33-126` contains only 26 outline glyphs and no whitespace/non-ASCII outline.
- `src/runtime/runtime_font.c:35-231` wraps vendored stb_truetype; `src/lib/nogc_sync_mut/io/font_sffi.spl:24-82` is the existing Simple owner facade.
- The dynamic `spl_fonts` path is richer but currently fails the focused interpreter suite on unresolved `rt_string_data`.

## Gaps and Risks

- No owned, non-vendored TTF/OTF fixture or real-font public-facade test exists.
- `GlyphCache.lookup` scans up to 512 entries and eviction slices/copies the array.
- Dynamic SFFI rasterization allocates argument arrays and performs a WFFI call per glyph pixel.
- Built-in vector rasterization scans every output sample against every outline edge.
- Accelerator fallback reparses environment payloads on each uncached glyph.

## Baseline

- `engine2d_text_spec.spl --mode=interpreter`: PASS for existing bitmap text.
- `font_renderer_spec.spl --mode=interpreter`: FAIL 14/15 on unknown extern `rt_string_data` when browser defaults try to load a font.
- Logs: `build/simple-2d-vector-fonts/`; do not rerun these unchanged in this session.

## Reuse Decision

Reuse `FontRenderer`, the existing font I/O owner, Engine2D readback, and bitmap regression surfaces. Do not add a parser, shaping engine, GPU atlas, or dependency.
