# JIT: `if val` on `f64?`, `Option<f32>`, `Option<u64>` yields garbage

- **Date:** 2026-11-06
- **Status:** fixed in source 2026-11-06 (awaits seed redeploy; 81a4145fbce had fixed only `Option<f64>`)
- **Severity:** P2 (wrong value)
- **Area:** `hir/lower/stmt_lowering.rs` `optional_enum_payload_inner`, MIR `rt_unwrap_or_self` decode

## Defect

JIT `if val x = <f64? | Option<f32> | Option<u64>>` binds a raw/tagged word instead of the
payload. `Option<f32> ?? 7.0` also prints a raw word. `Option<u64> ?? 0` prints 5 but
`a + 1` prints `<invalid-heap:0x29>` (same on the pre-fix binary). `Option<u64>` was excluded
from the `??` payload fix in 81a4145fbce on purpose (it printed 40, still tagged).

## Fix (2026-11-06)

- `hir/lower/stmt_lowering.rs` `optional_enum_payload_inner`: add `F32`, `U64` (enum form `Option<f32>` / `Option<u64>`
  `if val` now binds the raw payload type); Pointer-form arm also admits `F32`/`F64`.
- `hir/lower/expr/control.rs` `lower_coalesce`: `U64` joins the `Option<scalar>` presence/payload set (`rt_is_some`),
  so `None ?? 7` takes the default and the result is a raw u64.
- `mir/lower/lowering_expr_builtin.rs`: the `rt_unwrap_or_self` -> `U64` result is decoded with `rt_value_as_u64`
  directly (the `Option<u64>` enum slot is not `slot_holds_tagged_value`, so `unbox_scalar_for_raw_slot` skipped the
  decode and left the tagged word: 5 printed as 40; full-width u64::MAX now round-trips).
- `f64?` / `f32?` / `u64?` pointer forms were already correct on this base (verified, pinned by spec).

Evidence: `test/01_unit/language/jit_option_f32_u64_payload_spec.spl` RED 2/5 -> GREEN 5/5.
