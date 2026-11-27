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

## Source-admission annotation repair (2026-10-30)

A bounded static admission inventory for the current-release generic hardening lane found the existing build_session.spl marker carried a trailing colon in its bug ID and unkeyed explanatory prose. The canonical marker parser rejects that identifier. Keep the already registered ID unchanged, remove the colon, and label the same explanation with reason=. The marker still immediately precedes the same if block; executable behavior is unchanged. This repair is source-admission evidence, not a new generic-inference runtime PASS.

**Status:** FIXED (row closed 2026-11-02: E-MONO-032/033 were emitted only by src/compiler/40.mono, deleted by 200a05f5bc8 (refactor(compiler)!: delete monomorphization, merged on release/1.0.0); git grep E-MONO-032 over src/compiler finds nothing and src/compiler/40.mono is absent)

## WA-S6 verification and retirement (2026-11-26)

Retired `@workaround bug=mono_generic_fn_value_arg_2026-10-27` in
`src/compiler/80.driver/session/build_session.spl`: `keep<T>` now delegates
directly to `keep_with(k, value, _sffi_session_rc_share)`. Verified via
pure-Simple HIR/MIR lowering of both the defining `keep<T>` ->
`keep_with(k, value, share_val)` module (`target_idx = 0`, matching `k.all_ok =
k.all_ok and ok`) and caller module (`target_idx = 1`) in
`test/01_unit/compiler/mir/wa_src_lane6_reexport_and_route_lowering_spec.spl`,
`build_session_end_spec.spl` (`8/8` `--mode=interpreter`), and direct
`build_session.keep` regression coverage against a live `RuntimeValue` handle in
`test/01_unit/compiler/driver/wa_src_lane6_driver_workarounds_spec.spl` (`3/3`).
