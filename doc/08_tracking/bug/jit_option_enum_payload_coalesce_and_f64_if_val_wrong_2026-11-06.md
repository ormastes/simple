# JIT: `Option<i64> ?? x` and f64 `if val` payloads yield wrong values

- **Date:** 2026-11-06
- **Status:** fixed (2026-11-06)
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

## Resolution (2026-11-06)

Re-probed after 6d4699708dc: `Some(5) ?? 9` already gave 5, but `None ?? 9` on an explicit
`Option<i64>` unwrapped the real `None` (`<invalid-heap:0x9>`) because `lower_coalesce` tested
presence with `!= nil`. Fixes:

- `hir/lower/expr/control.rs` `lower_coalesce`: an explicit `Option<scalar>` enum subject now uses
  `rt_is_some` for presence and types the result as the raw payload scalar (MIR then decodes via
  `slot_holds_tagged_optional`). `None ?? 9` -> 9, `Some(0.1) ?? 7.0` -> 0.1.
- `hir/lower/stmt_lowering.rs` `optional_enum_payload_inner`: `F64` added, so `if val x = <Option<f64>>`
  binds a typed f64 (was raw word 576601489791778816 for a call subject, 0.09999999999999998 for a local).
- Verified under `SIMPLE_JIT_STRICT=1`; option/if-val/coalesce specs unchanged vs before binary
  (pre-existing failures in `option_i64_flat_lane_class_spec` 2/3 and `unwrap_payload_receiver_spec` 2/2 identical on both).
