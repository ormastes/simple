# Stage 2 resolver prefers `mod.spl` over `__init__.spl` (seed prefers `__init__.spl`)

Status: open (resolver divergence); the one observed victim is worked around.

## Divergence

A directory that holds both `mod.spl` and `__init__.spl` resolves differently:

- Seed: `src/compiler_rust/compiler/src/module_resolver/resolution.rs` probes
  `__init__.spl` first, then `mod.spl`.
- Pure-Simple: `src/compiler/80.driver/driver_source_loading.spl`
  (`_driver_try_entry_import_rel`, `_driver_resolve_entry_import_exact`, the
  numbered-dir helper) and `src/app/io/_CliCompile/native_build*.spl`
  (`_nb_resolve_*`) probe `mod.spl` first.

About 200 directories under `src/` contain both files, including compiler
packages (`80.driver`, `70.backend/backend`, `60.mir_opt/mir_opt`), so the two
compilers can bind different facades for the same `use` path.

## Observed failure

`src/lib/nogc_sync_mut/sffi/` has a comment-only `mod.spl` and an `__init__.spl`
that bare-exports `DynLib, DynLoader, sffi_lib_path, sffi_call`. Stage 2
resolved `use std.nogc_sync_mut.sffi.{DynLib, sffi_lib_path}`
(`src/lib/scv/wasm_executor.spl`) to the empty `mod.spl`, never loaded
`__init__.spl`/`dynamic.spl`, and the scv link-ladder rung died with the HIR
fatal `module std.nogc_sync_mut.sffi has no exported item DynLib`.

Workaround landed: wasm_executor imports `std.nogc_sync_mut.sffi.dynamic`
directly (pinned by
`test/01_unit/compiler/80.driver/scv_wasm_executor_sffi_import_resolution_spec.spl`).

## Open decision

Flipping the Stage 2 probe order to the seed's changes resolution for every
dual-file directory, including the self-host closure, and needs a full
bootstrap run to admit. Alternatively delete or merge the redundant
`mod.spl`/`__init__.spl` pairs so the order no longer matters.
