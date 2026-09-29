# skia shaper path: rt_font_load / rt_font_glyph_index externs missing

Date: 2026-09-16

## Observed
After repairing stale spec imports (spec pointed `std.nogc_sync_mut.io.font_ffi`,
which is a facade to `std.gc_async_mut.io.font_ffi`; the actual
`load_font`/`free_font`/`get_line_height` live in
`src/lib/nogc_sync_mut/io/font_sffi.spl` and return `FontHandle?`), examples fail
at runtime with:

- `semantic: unknown extern function: rt_font_load`
- `semantic: unknown extern function: rt_font_glyph_index`

Affected:
- `test/01_unit/lib/skia/shaper_spec.spl` — 9 of 64 fail (55 pass after the
  import fix); also 1 script-classification failure: "ASCII boundary 0x007F is
  Latin": `expected Script::Common to equal Script::Latin`
- `test/unit/lib/skia/shaper_spec.spl` (twin) — 3 of 58 fail on the same externs
- `test/01_unit/lib/skia/selected_arabic_spec.spl` — 1 of 1
- `test/01_unit/lib/skia/selected_devanagari_spec.spl` — 2 of 2

This matches the known unbacked-extern class
(`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`): these
externs are declared but have no runtime backing in the deployed binary.

## Impact
Real-font shaping oracles (HarfBuzz-pinned Arabic/Urdu/Devanagari) and
attached-font fallback selection cannot run; they fail closed with an extern
error rather than silently, but coverage is zero for those paths.

## Expectation
`rt_font_load` and `rt_font_glyph_index` are backed in the native runtime (or
given pure-Simple implementations), and 0x007F classifies as `Script::Latin`.

## Unblock condition
Add runtime backing for `rt_font_load` / `rt_font_glyph_index` (check
`scripts/check/unbacked_extern_baseline.txt` census class for these symbols),
fix the 0x007F script boundary in the shaper's classifier, re-run the four
specs.
