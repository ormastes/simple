# Browser Color Parsing Commonization Blocked

**Date:** 2026-05-10
**Component:** browser_engine/dom.spl, common/color/
**Severity:** Low (tech debt)
**Status:** Blocked

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

## Resolution Path

1. Fix Cranelift `f64?` optional codegen bug
2. Either adopt `Color` struct in browser or add `to_u32()`/`from_u32()` to common
3. Expand common named color table to CSS Level 4 (148 entries)
4. Then sweep-refactor dom.spl color parsing to delegate to common/color/

## Related
- Timing commonization: completed (commit 6c07c3d)
- Layout commonization: blocked by i32/i64 + DOM-coupling architectural mismatch
