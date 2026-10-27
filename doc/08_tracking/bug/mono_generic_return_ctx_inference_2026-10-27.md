# Mono cannot infer a generic return-only type parameter from the expected type (E-MONO-032)

- id: mono_generic_return_ctx_inference_2026-10-27
- severity: P1 (blocked phase-3 run 6 at monomorphize, 13 failures)
- found: phase-3 run 6, stage2 `ef0681fc0e1`, windows-gnu/llvm-mingw

## Symptom
`fn rti_err<T>(code: text, message: text) -> Result<T, RtiError>` called as
`case X: rti_err(...)` / `return rti_err(...)` where the enclosing function's
return type fixes `T`. Mono reports
`E-MONO-032: call to generic rti_err ... has no explicit type args` and
`E-MONO-033` refuses to lower 13 call sites in
`src/compiler/20.hir/return_type_interface_v1.spl`.

## Workaround (tagged `@workaround bug=mono_generic_return_ctx_inference_2026-10-27`)
Helper made non-generic (`rti_error -> RtiError`); callers write `Err(rti_error(...))`.

## Real fix
Infer a type parameter that appears only in the return type from the call's
expected type (return position / match arm / `return` expr) during HIR type
checking, so mono receives explicit type args. Remove the workaround after.
