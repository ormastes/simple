# `if val` binding from a generic `T?` return stays optional under ERR-01

Date: 2026-11-13
Status: FIXED (seed source 2026-11-13; verified on a seed built from it)
Severity: P3
Found by: lane p3-asyncreg-20261113 (async_handler_registry_removed_apis_2026-09-16)

## Observed

The ERR-01 diagnostic (seed fix `349cd121b82`, `hir/lower/expr/operators.rs`
`lower_cast`) says to narrow with `?? <default>`, `if val x = ...`, or
`match`. `if val` does not work when the optional comes from a generic return:

```simple
use std.concurrent.channel.{channel_new}
fn drain() -> i64:
    val ch = channel_new()
    ch.send(41)
    if val m = ch.try_recv():      # Channel.try_recv<T>() -> T?
        return (m as i64) + 1      # still: cannot cast an optional `T?` to `i64` (ERR-01)
    return 0
```

Measured with seed-fix 2026-11-13: the spec fails with `err01=2`, 0 examples
executed. These all pass (1/1) on the same seed: `?? 0`, `match Some(v)`,
`if val` over a concrete `Dict<i64,i64>.get`, and a typed binding first
(`val m: i64? = ch.try_recv()` then `if val n = m`).

## Expectation

`if val x = <expr of type T?>` binds `x: T` whether `T` is concrete or an
uninferred generic. Either that, or the diagnostic stops recommending
`if val` for this case.

## Workaround in tree

`src/lib/nogc_async_mut/http_server/worker_owner.spl` run loop uses the
typed-binding form.

## Resolution (2026-11-13, lane p3-ifval-20261113)

Root cause: with `T` uninferred, the subject of `if val m = pick(..)` /
`ch.try_recv()` is the registry optional over `any` (`any?`). The seed's single
if-let binder `build_if_let_binding_stmts`
(`src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs`) narrowed
BoxInt/bool/u64/f32/f64 scalars and array/text/struct/enum payloads, and kept
every other subject typed as the optional, so `m` stayed `any?` and
`lower_cast` raised ERR-01 on the narrowing ERR-01 itself recommends.

Fix: an `any?` subject binds plain `any`, mirroring `lower_coalesce`'s
`any? ?? d -> any` arm (`349cd121b82`). The payload word of an erased optional
is the tagged RuntimeValue an `any` slot holds, and MIR's `rt_unwrap_or_self`
lowering does not unbox an `any` result, so no representation changes. One
owner covers `if val`, `elif val`, the expression form and `while val`.
ERR-01 (`lower_cast`, `is_optional_source_type`) is unchanged: the
un-narrowed `pick(..) as i64` and `val m = pick(..); m as i64` are still
rejected.

Evidence (aarch64, base = seed-fix 2026-11-13, fixed = seed built from this lane):
- `test/01_unit/language/if_val_generic_optional_cast_spec.spl` (run with
  `SIMPLE_BINARY=<seed>`): base 3/7 -> fixed 7/7 (5 positive incl. channel
  `try_recv`, JIT `while val`, interpreter leg; 2 ERR-01 negatives pass on both).
- cargo `hir::lower::tests::expression_tests::if_val_on_generic_optional_binds_payload_for_numeric_cast`:
  red before (ERR-01 on the narrowed statement-form binding), green after.
  `hir::lower mir::lower casting`: base 1062 passed / 6 failed -> fixed 1063 / 5;
  the 5 are pre-existing and unrelated.
- `test/01_unit/compiler/hir/optional_as_cast_rejected_spec.spl` (pure-Simple
  lowerer): 3/3 on both; that lowerer has no if-val false positive, the new
  example pins it.

Residuals filed: `interp_while_val_binds_option_not_payload_2026-11-13`,
`pure_err01_untyped_local_of_optional_call_not_rejected_2026-11-13`.
The `worker_owner.spl` typed-binding workaround can be reverted to the direct
`if val` once a seed carrying this fix is deployed.
