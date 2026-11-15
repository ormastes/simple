# `--no-mangle` emits module-qualified symbols (simple-core runtime archive unlinkable)

- **Status:** verification-pending
- **Date:** 2026-11-16
- **Area:** compiler / MIR naming + LLVM backend symbol naming

## Symptom

`check-simple-core-runtime-smoke.shs` (roster gate, line ~255) fails with
`missing_required_symbol:rt_string_replace`. The archive
`build/os/simple-core-simpleos/libsimple_runtime.a` built by the phase-2
compiler exports all 872 text symbols module-qualified, e.g.
`runtime.simple_core.core_string.rt_string_replace`; none are bare.

Repro (WSL, `~/fixC2`):

```
native-build --backend llvm --source src/runtime/simple_core --entry-closure \
  --entry src/runtime/simple_core/core_math.spl --no-mangle --emit-archive ...
nm -g out.a | grep ' T '
  T runtime.simple_core.core_math._sffi_core_math_sqrt
  T runtime.simple_core.core_math.rt_math_sqrt
```

The same result came from `~/xc/simple-p2` (ef09036bfa8f) and from
`~/xc/simple-p2.prev2` (the 16:34 build), on both the per-file route and the
`SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` route. So this is not a regression
between those two builds.

## Root cause

Two layers were at fault:

1. **MIR naming.** `mir_provider_function_name_fields_v1`
   (`src/compiler/50.mir/_MirLowering/provider_metadata.spl`) passes every
   non-extern, non-export function name through
   `mir_provider_callable_identity`, which yields `<module>.<name>`. That name
   is used for definitions and for cross-module call links. Both
   `MirToLlvm.llvm_function_symbol_name` and Cranelift's
   `cl_function_emit_name` return the MIR name unchanged under `--no-mangle`,
   so the qualification reached the object file.
2. **LLVM ordering (latent).** Commit 22f021ced66 (2026-11-10) moved the
   runtime-owned rename (`rt_*` -> `__simple_local_rt_*`) ahead of the
   `no_mangle` check. With bare MIR names, every `rt_*` definition would have
   been privatized as well. The qualified names hid this.

## Fix

- `mir_provider_callable_identity_for_mode` drops exactly the `<owner>.`
  prefix when `SIMPLE_NATIVE_BUILD_NO_MANGLE=1`. `Type.method` is kept as is.
  Definitions and call sites share this function, so they stay linkable.
- `mir_no_mangle_claim_leaf` (called from function lowering) fails closed with
  a fatal MIR error when two modules in one compilation define the same leaf.
- In `MirToLlvm.llvm_function_symbol_name`, `no_mangle` is checked before the
  runtime-owned rename again.
- Cranelift is unchanged. Its no-mangle path still privatizes `rt_*`
  definitions, because its array-literal lowering declares the bare runtime
  symbol outside `func_handles`. Open follow-up: a Cranelift `--no-mangle`
  runtime archive will lack bare `rt_*` definitions.

Spec: `test/01_unit/compiler/70.backend/no_mangle_leaf_symbol_spec.spl`.

## Verification still needed (native)

Rebuild the phase-2 compiler from this change, then rerun
`scripts/check/check-simple-core-runtime-smoke.shs`. Check:

- `nm -g libsimple_runtime.a | grep ' T '` shows bare `rt_*` names.
- `nm -u` on the parts shows no `runtime.simple_core.*` references.

The in-process collision check sees only one process's closure. The archive
gate in the smoke script combines per-entry parts with `ar`, and that step
does not reject duplicate definitions across parts.
