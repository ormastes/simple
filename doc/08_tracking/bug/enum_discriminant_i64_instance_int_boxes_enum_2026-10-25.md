# `_sffi_enum_discriminant<i64>(enum_value)` int-boxes the enum, so the discriminant is -1
## Fixed 2026-10-25 at the source (expr_dispatch.spl, 23 sites); type-checker hole still open

Date: 2026-10-25. Lane: Phase 3 bootstrap (run-27e) B9, compiler-fix agent.

## Symptom

In the Stage-2-built Phase 3 compiler, every `*_disc` probe in `lower_expr_impl`
failed: `_sffi_enum_discriminant<i64>(HirExprKind.Call(...))` returned -1, and
lowering reported `unsupported MIR expression` (disc=23 Call). The bypass agent
NOPed the `rt_value_int_wide` call in the `$i64` instance by binary patch
(`switch_operators_calls_p3b9.o`).

## Root cause

`_sffi_enum_discriminant<T>(value: T)` forwards `value` to the generic extern
`rt_enum_discriminant<T>`, whose parameter is a runtime value. The extern call
boundary boxes any I64-typed argument with `rt_value_int_wide` (`box_runtime_value`).
Writing `<i64>` makes `T = i64`, so inside that instance the enum handle is an
I64 local and becomes `handle << 3`. `rt_enum_discriminant` then sees a
non-enum word and returns -1. With `<HirExprKind>` / `<MirTypeKind>`, the
local has an enum MIR type and passes through untouched.

Minimal repro (`disc_of<T>` mirroring the helper), Stage 2:
`disc_of<Shape>(Shape.Box(w: 4))` -> `1`, `disc_of<i64>(Shape.Box(w: 4))` -> `-1`.

## Fix

All 23 `_sffi_enum_discriminant<i64>(...)` sites in
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` now name the argument's real
enum type (`MirTypeKind`, `HirExprKind`, `HirBinOp`, `HirUnaryOp`). The same
functions already used these instances, for example `<HirExprKind>` at
`binary_disc` and `<HirUnaryOp>` at `op_disc`. No `<i64>` instance remains in `src/`.

## Still open

The type checker accepts an enum argument for an explicit `T = i64` type
argument (`disc_of<i64>(Shape.Box(w: 4))` compiles). It should reject it.
Until it does, the same mistake can be reintroduced silently.
