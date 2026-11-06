# JIT: `Option<i64> ?? x` and f64 `if val` payloads yield wrong values

- **Date:** 2026-11-06
- **Status:** open
- **Severity:** P2 (wrong value)
- **Area:** `src/compiler_rust/compiler/src/mir/lower/lowering_expr_builtin.rs`

## Defect

Probed on the release/1.0.0 seed with the JIT `run` lane, both before and after 6d4699708dc:

- `Option<i64>` holding `Some(5)` with `?? 9` gives 40 instead of 5. The code comment near
  `lowering_expr_builtin.rs:~340` lists `??` as covered, but the explicit `Option<T>` enum form
  is not unboxed on that path.
- `if val x = <f64? or Option<f64>>` prints a raw tagged word (611363786854498304) instead of
  the float.

6d4699708dc fixed the `if val` path for i64, bool and u8 payloads of `Option<T>`. Extend the
same `slot_holds_tagged_optional` unboxing to the `??` path and to f64 payloads.
