# Browser Color Parsing Commonization Blocked

Status: Resolved (2026-05-19)

**Date:** 2026-05-10
**Component:** browser_engine/dom.spl, common/color/
**Severity:** Low (tech debt)
**Status:** Resolved (2026-05-19)

## Problem

`src/lib/gc_async_mut/gpu/browser_engine/dom.spl` contains ~500 lines of CSS color
parsing (lines 1048-1700) that partially duplicates `src/lib/common/color/convert.spl`.
Cannot consolidate due to three blockers:

## Blockers

### 1. Cranelift f64? Optional Bug
dom.spl uses manual integer parsers (`pcc_parse_int`, `hex_byte`, `hex_nibble`,
`hex_digit`) that return concrete types instead of `f64?` optionals. This works
around a known Cranelift codegen bug with `f64?` in compiled mode. Switching to
common/color functions that return `Color?` or use optional intermediates would
hit this bug.

### 2. u32 vs Color Type Mismatch
- Browser engine uses packed `u32` RGBA throughout (0xRRGGBBAA)
- Common library uses `Color(r: i64, g: i64, b: i64, a: i64)` struct
- Every color callsite in the browser would need conversion wrappers

### 3. Named Color Table Size
- dom.spl: 148 CSS Level 4 named colors (full spec)
- common/color/convert.spl: 25 named colors
- Would need to expand common table to 148 entries to avoid regression

## Resolution (2026-05-19)

All three blockers resolved without waiting for the Cranelift f64? fix:

1. **Blocker 1 — Cranelift f64? bug**: Worked around by using pure integer arithmetic
   throughout `parse_css_color`. No `f64?` optionals anywhere in the color parse path.

2. **Blocker 2 — u32 vs Color type**: Resolved by:
   - `parse_css_color` in `css.spl` returns `i64` (ARGB packed, same bit layout as engine2d u32)
   - `Rgba8.to_u32()` / `Rgba8.from_u32()` added to `common/engine/color.spl`
   - Browser code can call `parse_css_color` then pass the i64 directly to renderer

3. **Blocker 3 — named color table**: `css_named_color` in `css_named_colors.spl` covers CSS Level 4
   (148 unique names including `rebeccapurple`; grey/gray synonyms handled via `or` branches;
   `css.spl` normalizes input with `.trim().to_lower()` before calling the table).

**Files changed:**
- `src/lib/gc_async_mut/gpu/browser_engine/css.spl` — added `parse_css_color`,
  `css_color_r/g/b/a`; delegates named-color lookup to `css_named_colors.spl`
- `src/lib/gc_async_mut/web/css_named_colors.spl` — `css_named_color` with 148 CSS L4
  names (grey/gray synonyms via `or` branches; input normalized via `.trim().to_lower()`)
- `src/lib/common/engine/color.spl` — added `Rgba8.to_u32()` and `Rgba8.from_u32()`

**Next step:** When color parsing is added to `dom.spl`, delegate to `parse_css_color`
from `std.gc_async_mut.gpu.browser_engine.css`.

## Re-verification (2026-05-29)

Confirmed all three blockers resolved:
- `parse_css_color` / `css_color_r/g/b/a` present in `css.spl` (186 lines)
- `Rgba8.to_u32()` / `Rgba8.from_u32()` present in `common/engine/color.spl`
- `css_named_colors.spl` covers 148 unique CSS L4 names (grep -oE '"[a-z]+"' | sort -u | wc -l = 148)
- `dom.spl` reduced to 124 lines; manual parsers (`pcc_parse_int`, `hex_byte`, etc.) absent
- `css.spl` calls `.trim().to_lower()` before `css_named_color()` — case normalization confirmed

## Related
- Timing commonization: completed (commit 6c07c3d)
- Layout commonization: blocked by i32/i64 + DOM-coupling architectural mismatch
