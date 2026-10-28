# Mono cannot infer T when a generic function is passed as a fn value (E-MONO-032)

- id: mono_generic_fn_value_arg_2026-10-27
- severity: P1 (blocked phase-3 run 8 at monomorphize; 6 sites unspecialized)
- found: phase-3 run 8, stage2 `ef0681fc0e1`, sources `6a59a752d10`, windows-gnu/llvm-mingw

## Symptom
In `keep<T>(k, value: T)`, the call `keep_with(k, value, _sffi_session_rc_share)` passes the
uninstantiated generic `_sffi_session_rc_share<T>` as a `fn(T) -> bool` value. Mono reports
`E-MONO-032: call to generic keep_with at build_session.spl:93:5 ... argument inference has no
concrete local type`, then `E-MONO-033` (6 unspecialized sites).

## Workaround (`@workaround bug=mono_generic_fn_value_arg_2026-10-27`)
`keep` inlines the share call instead of passing the generic function as a value. Same behaviour.

## Real fix
When a generic function is used as a value whose expected type is `fn(T) -> R` and `T` is bound
in the enclosing generic context, instantiate it with that `T` (and infer the callee's `T` from
the enclosing substitution). Remove the workaround after.
