# A match expression whose FIRST arm is `panic(...)` yields const 0

**Status:** open

## Open 2026-10-25 — compiler fix in `50.mir/_MirLoweringExpr/switch_operators_calls.spl`; takes effect on the Phase 3 self-rebuild

Date: 2026-10-25. Lane: Phase 3 bootstrap (run-27e), compiler-fix agent.

## Symptom

```
val admission: Adm = match parser_provider_v1_admit(..):
    case Err(reason): panic("...")
    case Ok(value): value
```

Natively compiled by Stage 2 (cranelift, aarch64), `admission` is a constant
zero: a struct payload SEGVs on its first field load (`mov x2,#0; ldr x1,[x2]`
in `build_module_from_flat_pool_blob`, `module_assembly.spl:1437` and `:1547`),
an i64 payload silently reads 0. Not affected: Ok arm first, `return` as the
first arm, statement-form `match` with an assignment.
Repro: `src/app/zz_p3s1/m.spl`, `m2.spl` in worktree `simple-p3fix-p3s1`.

## Root cause

`lower_bootstrap_panic_call` terminates the block with `Abort` and then
switches to a fresh `after_panic` block, returning a **Unit** temp. Every
match-arm merge in `switch_operators_calls.spl` guarded the arm-result copy
only with `current_block_has_explicit_terminator()`, which is false in
`after_panic`. So the panic arm:

1. copied its Unit temp into the shared `result` local, and
2. set the first-wins `inferred_ty = Unit`.

The Ok arm's copy then landed in a local that the merge block retyped with
`set_local_type(result, Unit)`. The backend drops stores to a unit local and an
undefined cranelift variable reads as `iconst 0`.

`lower_if` already had this guard (`local_is_unit`, see
`native_if_print_only_arms_alloca_void_2026-07-11.md`); the match lowerers did
not.

## Fix

All 8 arm/default copy sites in `switch_operators_calls.spl`
(scalar match, if-chain match, guarded scalar match, enum match arms,
guarded catch-alls, enum default) now skip a Unit-typed arm result exactly as
`lower_if` does: no copy, no type inference, no struct-name propagation. A
match whose arms are ALL unit falls to the existing `result_defined == false`
const-0 placeholder, which is what `lower_if` does too.

## Verification

- Red: Stage 2 (old compiler) builds the spec fixture and prints the wrong
  value (`vf=1`, want 42; struct variant SEGVs).
- The patched module compiles with Stage 2.
- Green: deferred. Stage 2 has the old MIR lowering compiled in; the fix takes
  effect when the Phase 3 compiler rebuilds itself. Spec:
  `test/01_unit/compiler/codegen/native_match_panic_first_arm_spec.spl`.

Source workaround (separate, other agent): reorder arms Ok-first at
`module_assembly.spl:1437/1547`.
