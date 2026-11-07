# Lifted lambda entry hooks shift parameter and environment slots

Status: source repair and regressions authored; runtime validation pending an admitted self-hosted producer.

## Boundary and cause

`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`,
`lower_lambda_value_for_type`, called `emit_mcdc_worker_registration` before
calculating `locals.len() - arity`. The registration emits non-unit calls,
which allocate result temporaries. MC/DC modes 1 and 2 therefore shift the
calculated argument offset by one; RT-HAL registration can shift it too.

For `fn identity() -> fn(i64) -> i64: \\x: x`, the lifted return reads the
hook's bool temporary instead of Arg0. For a capture `\\x: x + k`, the lifted
`rt_closure_get_capture` receives Arg1 (the user parameter) instead of Arg0
(the closure handle). The latter can dereference a non-environment value.
These are source-derived consequences, not executed runtime observations.

## Repair and prevention

Freeze the argument offset immediately after `begin_function`, before any
entry hook can add locals. Keep the hook before capture reads and user code.

- Minimal executable source: `test/fixtures/compiler/lambda_prologue_slots/main.spl`.
- MIR regression: `test/01_unit/compiler/50.mir/lambda_prologue_argument_slots_spec.spl`.
- Six cases cover modes 0/1/2, each with and without a capture. They assert
  the exact `LocalKind.Arg` index used by the return/arithmetic and environment
  getter, one capture read where expected, and hook-before-read order.

## Evidence limits

Source inspection establishes that `emit_mcdc_worker_registration` returns
bool and `MirBuilder.emit_call` allocates a temporary for non-unit results.
The regression must be executed with an admitted current self-hosted runtime;
source checks alone do not establish runtime PASS. No seed fallback is admitted.
