# Stage4 env paths emitted an undeclared `variables` LLVM global

- **Date:** 2026-08-03
- **Status:** FIX IMPLEMENTED — STAGE4 VERIFICATION PENDING
- **Severity:** P1
- **Area:** pure-Simple HIR import ownership
- **Owner:** `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`
- **Exact source:** `src/lib/nogc_async_mut/env/paths.spl`

## Recorded failure

The real Stage4 entry closure reached `env/paths.spl` and failed LLVM
validation with:

```text
llvm codegen: semantic: llvm global load referenced undeclared symbol variables
```

The source selectively imports `env_get` through
`use std.env.variables.{env_get}`. A qualified module tail must not escape HIR
as a value receiver when the selected callable has already been bound to its
retained physical `ModuleSurface` owner.

## Owner repair

Module import lowering now resolves aliases through the aligned retained
surface index and registers imported callables against that physical owner.
Module-only namespace symbols use the same owner. This avoids lowering an
alias-only namespace receiver as `LoadGlobal` while keeping real unresolved
globals fail-closed at the LLVM boundary.

## Regression evidence (2026-08-17)

`test/01_unit/compiler/hir/module_namespace_retained_surface_spec.spl` now
covers the previously missing selective-import topology directly:

- exact `use std.env.variables.{env_get}`;
- adjacent `use std.env.variables.{env_get as read_env}`;
- no MIR `LoadGlobal` named `variables` or ending in `.variables`;
- a direct call whose terminal owner is `env_get`.

The deployed pure-Simple macOS test runner passed all five cases. A focused
pure-Simple native shard compile of the real `env/paths.spl` also passed the
historical undeclared-global point, then stopped later with the separate
diagnostic `runtime error: field access on nil receiver`; it did not produce a
fresh Stage4 artifact. Therefore this row remains verification-pending rather
than fixed.

## Closure gate

Run one provenance-admitted current Stage4 entry closure. Close the row only
when the real env paths shard emits no undeclared `variables` global, LLVM
verification passes, and the Stage4 binary is produced. Track the later nil
receiver independently if it reproduces on the admitted current compiler.
