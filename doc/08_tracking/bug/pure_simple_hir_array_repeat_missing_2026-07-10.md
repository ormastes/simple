# Pure-Simple HIR Array-Repeat Lowering Missing

- **Date:** 2026-07-10
- **Status:** open
- **Area:** HIR/MIR collection lowering

`[value; count]` is parsed as `ExprKind.ArrayRepeat`, but pure-Simple HIR has no
corresponding expression variant or lowering path. A native entry using
`[0 as u32; 16]` therefore produced an undefined MIR local instead of calling
the existing `rt_array_repeat` runtime helper.

The fix must cover HIR construction, semantic/safety/effect traversal,
monomorphization, const evaluation, interpreter behavior, and MIR lowering for
dynamic counts. A SIMD-only literal expansion is not acceptable.
