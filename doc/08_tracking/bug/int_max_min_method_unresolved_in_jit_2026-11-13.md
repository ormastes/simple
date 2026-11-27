# Integer `.max()` / `.min()` method calls fail: `Function 'i64.max' not found`

- **Date:** 2026-11-13
- Status: verification-pending
- **Lane:** seed `run`/`test` (JIT-first), phase-1 seed `C:/dev/wt/p1-20261112/.../bootstrap/simple.exe`
- **Found by:** llm_caret yoga coverage (`resolveGap` crashed on any node with children)

## Repro

```simple
fn main():
    val y = 5
    print "{y.max(9)}"
```

Output: `Runtime error: Function 'i64.max' not found` followed by the
"unresolved symbol -- code-generation dispatch gap" refusal. A typed `val x: i64`
receiver and a call-result receiver (`f().max(0)`) fail the same way.

## Root cause

The 2026-08-10 fix (`float_and_int_math_methods_missing_on_numeric_receivers_2026-08-10.md`)
wired `max`/`min` for FLOAT receivers only (routed to `rt_math_max`/`rt_math_min`)
and integer `abs` (`iabs`). In
`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs::try_compile_builtin_method_call`
(and the mirror in `codegen/instr/methods.rs`) an integer receiver for
`max`/`min`/`clamp` falls through to static dispatch, which looks up a
non-existent `i64.max` function. The interpreter path
(`interpreter_method/primitives.rs`) does implement int `max`/`min`/`clamp`,
so the two lanes disagree.

## Fix direction

Lower integer `max`/`min` to Cranelift `smax`/`smin` (`umax`/`umin` for
unsigned), and `clamp` to the pair, in both dispatch sites. Stamp the integer
result type in `hir/lower/expr/mod.rs::builtin_numeric_method_result_type`.
Add rows to `scripts/check/check-numeric-method-family-dispatch.shs`.

## Workaround in tree

`src/app/llm_caret/claude_full/native_ts/yoga_layout/index.spl` uses a local
`nonNegative()` helper instead of `.max(0)`.

## Fix (2026-11-13, work/jit-intmax-20261113)

- Seed JIT: `codegen/instr/methods.rs::emit_int_min_max` lowers integer
  `max`/`min`/`clamp`/`abs` to `smax`/`smin` (`umax`/`umin` for unsigned; u64
  `abs` is identity), called from both `compile_builtin_method` and the
  qualified-receiver path in `closures_structs.rs::try_compile_builtin_method_call`.
  HIR stamps the receiver type as the result (`builtin_numeric_method_result_type`).
- Pure-Simple MIR (`50.mir/_MirLoweringExpr/builtin_method_extras.spl`): had
  signed `max`/`min`/`abs` only; added `clamp` and unsigned `max`/`min`/`clamp`
  (operands cast to the unsigned receiver type, so LLVM/Cranelift adapters pick
  `ult`/`ugt`). Known residual: the native `isel_x86_64` backend's `Lt`/`Gt`
  are signed-only for every unsigned compare (pre-existing, not specific to this).
- Workaround removed: yoga `resolveGap` uses `g.max(0)` again.
- Spec: `test/01_unit/compiler/50.mir/int_min_max_methods_spec.spl` (in-process,
  `simple run` subprocess, MIR lowering); guard rows added to
  `scripts/check/check-numeric-method-family-dispatch.shs`.
