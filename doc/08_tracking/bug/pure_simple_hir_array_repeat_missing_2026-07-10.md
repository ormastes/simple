# Pure-Simple HIR Array-Repeat Lowering Missing

- **Date:** 2026-07-10
- **Status:** RESOLVED — verified fixed at origin tip 8932fcb3a148
- **Area:** HIR/MIR collection lowering

`[value; count]` is parsed as `ExprKind.ArrayRepeat`, but pure-Simple HIR has no
corresponding expression variant or lowering path. A native entry using
`[0 as u32; 16]` therefore produced an undefined MIR local instead of calling
the existing `rt_array_repeat` runtime helper.

The fix must cover HIR construction, semantic/safety/effect traversal,
monomorphization, const evaluation, interpreter behavior, and MIR lowering for
dynamic counts. A SIMD-only literal expansion is not acceptable.

## Verification (2026-07-16)

Verified fixed at origin tip 8932fcb3a148: `probe08_array_repeat_a.spl` (`val arr = [0 as u32; 16]`, prints len, arr[0], arr[15]). Oracle: `bin/simple run` → `16` / `0` / `0`. Native: `native-build --entry --clean` exit 0, binary built, run → `1600` (all three concatenated, matches oracle). Array-repeat `[value; count]` now lowers correctly through pure-Simple HIR/MIR to a real 16-element zero-filled array.
