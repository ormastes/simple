# `simple run` had no font SFFI except rt_font_load_array (2026-10-04)

Status: FIXED in branch `work/interp-font-handles`.
Parent record: `browser_real_site_rendering_gaps_2026-10-04.md` (gap K).

## Symptom

www.wikipedia.org, once its script pass stopped stalling, failed at render
with `semantic: unknown extern function: rt_font_glyph_index` (multi-script
fallback in `src/lib/skia/feature/shaper/font_fallback.spl:71`) and, with
only that one wired, next with `rt_font_free`.

## Root cause

`src/lib/nogc_sync_mut/io/font_sffi.spl` declares 13 `rt_font_*` externs
over `src/runtime/runtime_font.c`; the seed interpreter registered only
`rt_font_load_array`, which returned the raw `FontData*` as an `i64` to
Simple code. Wiring the rest with plain `insert_simple!` would let a stale,
forged or double-freed integer reach C as a pointer (use-after-free).

## Fix

`src/compiler_rust/compiler/src/interpreter_extern/font.rs`: every raw
`FontData*` / `BitmapData*` lives in a handle table; Simple only sees an
opaque handle `(generation << 24) | (slot + 1)`. Free removes the entry and
bumps the slot generation, so use-after-free, double free and forged values
return a semantic error and never reach C. `rt_font_load_array` now returns
a handle too. Registered: `rt_font_load`, `_free`, `_glyph_index`,
`_glyph_bitmap`, `_glyph_advance`, `_line_height`, `_ascent`,
`_bitmap_width`, `_bitmap_height`, `_bitmap_get_pixel`, `_bitmap_free`.
Compiled code is unchanged (it still calls the C functions directly).

Tests: `cargo test -p simple-compiler --lib interpreter_extern::font` - 6
cases incl. a real-font round trip (Bungee-Regular.ttf), use-after-free and
double-free for fonts and bitmaps, forged/raw values, slot reuse.

## Not covered

`rt_font_read_u16/i16/u32` and `rt_font_find_table`
(`src/lib/skia/entity/glyph_outline.spl`) take byte arrays, not pointers,
and have no implementation in `src/runtime/` at all; they are a separate gap.
Non-Latin glyphs on wikipedia.org still render as tofu (fallback font
coverage, gap F).
