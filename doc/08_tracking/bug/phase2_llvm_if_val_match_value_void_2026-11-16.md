# Phase 2 LLVM backend: `if val ... else: match ...` used as a value lowers to void

Registered 2026-11-16. Status: fix-implemented-verification-pending (updated 2026-11-27). Severity P2.

## Symptom

Frozen Phase 2 compiler (`/c/dev/p3diag/p2.exe`, pin `18a1f28937c2`), LLVM
backend, codegen error:

```
unsupported LLVM value conversion from i64 to void function=...FileFiberTldrBridgeV1._drain_completions value=%l182 at src/compiler/80.driver/driver_build/file_fiber_tldr_bridge_v1.spl:329:16
```

## Source location

`FileFiberTldrBridgeV1._drain_completions` in
`src/compiler/80.driver/driver_build/file_fiber_tldr_bridge_v1.spl` (at
`origin/release/1.0.0` 115bd321a44, the `val completion = if val retained =
self.pending_completion:` binding, about lines 306-321). Shape:

```
val completion = if val retained = self.pending_completion:
    retained
else:
    val taken_completion: Result<RingCompletion<i64>?, SimpleRingError> = ...
    match taken_completion:
        case Err(error): return Err(...)
        case Ok(Some(value)):
            self.pending_completion = Some(value)
            value
        case Ok(_): return Ok(())
```

An `if val ... else:` used as a value whose else branch is a `match` where some
arms `return` and one arm yields a value. The merge value's type appears to be
lowered as `void` (the arms that `return` contribute a void/never type that
wins the join), then the `i64` value cannot be converted to it.

## Repro / reduction status

Not reduced. A 25-line candidate repro (a class with `pending: Cpl?` and a `me drain(n) -> Result<i64, text>` using `val completion = if val retained = self.pending: retained else: <match with return/yield arms>`) was written, but could not be compiled: `p2.exe native-build --backend llvm` was refused by the build memory guard ("1500 MiB of RAM/commit headroom free, below the 24576 MiB reserve (SIMPLE_BUILD_MEMORY_RESERVE_BYTES)") because a long build was running on the shared host, and `p2.exe compile` only supports `--format=smf`. The reserve was deliberately not lowered. Whether the minimal shape reproduces is therefore UNKNOWN, and the current seed was not tried. The only known failing instance is the full `_drain_completions` above.

## Workaround (build tree, NOT yet verified by codegen)

Use a `var completion_slot: RingCompletion<i64>? = self.pending_completion`,
then a statement-form `match` that assigns the slot or returns, then
`completion_slot.unwrap()`. This avoids the value-position `if val/else/match`.
It has not yet been confirmed through a codegen run.

## Fix Implemented (2026-11-27)

- `src/compiler/50.mir/mir_lowering_stmts.spl`:
  - Added `mir_join_slot_is_unit` (separating genuine `Unit`/`void` join slots from `Never` diverging-arm types) and hardened `mir_merge_arm_types` to ignore payloadless (`Unit`/`Never`) arms whenever merging against concrete value-yielding arms.
  - Updated `lower_if` and `lower_if_chain` so diverging/payloadless arms are excluded from branch result copies (`merge_result_is_payloadless`) and branch type unification while non-`Unit` merge destinations (`not result_slot_unit`) still receive `set_local_type(result, inferred_ty)` from concrete yielding arms, keeping all-diverging merges sound via `merge_has_incoming`.
- `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`:
  - Applied the same payloadless/diverging arm guards and `mir_merge_arm_types` unification across `emit_switch_dispatch`, `emit_if_chain_dispatch`, `lower_match`, `lower_guarded_scalar_match`, and `lower_enum_match_flat` (skipping dead `next_block`/cascade-tail emission once `closed` holds, and taking the early return on `not merge_has_incoming and (closed or self.builder.current_block_has_explicit_terminator())` so all-diverging guarded catch-all matches never fall into a dead merge with `Const(0, i64)`).

## Verification

- `test/01_unit/compiler/50.mir/if_val_match_diverging_value_type_spec.spl`: `9 examples, 0 failures` (`--mode=interpreter`, 2026-11-27), covering `mir_merge_arm_types`, typed and untyped `if val ... else: match ...` with `return Err` / `return Ok` and `Ok(Some(value))` yielding arms, `break`/`continue` loops, all-diverging `match`, standalone and `if val ... else: match ...` all-diverging guarded catch-all matches, and positive non-diverging control.
- `test/01_unit/compiler/50.mir/if_val_match_llvm_value_type_spec.spl`: `5 examples, 0 failures` (`--mode=interpreter`, 2026-11-28, Lane A), verifying full `HIR -> MIR -> MirToLlvm` lowering of untyped `_drain_completions` while-loop `if val ... else: match ...` struct shape, `f64` `if val`/`if-elif` chains with returning arms, `then`-returns/`else`-match-yields, and all-diverging `else` match with zero LLVM `codegen_errors` and zero `void` operands.
- `src/compiler/80.driver/driver_build/file_fiber_tldr_bridge_v1.spl:293` annotation updated to `ROOT-FIXED+STAGE2-GATED` while retaining the Stage-2-safe slot form until the frozen Phase 2 binary is rebuilt.
- Native LLVM Phase 2 backend rebuild verification remains pending (`fix-implemented-verification-pending`).

## Status

`fix-implemented-verification-pending` (MIR lowering fix + unit spec verified on interpreter; native Phase 2 LLVM backend rebuild verification pending).
