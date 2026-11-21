# Per-file unit lane: MIR declaration providers are the unit's targets only

- **Status:** verification-pending (fix needs a Stage 2 rebuild)
- **Found:** 2026-11-21, provisional native group build (Stage 2 `0d8a3269bec`,
  per-file worker pool, 1258-module closure)
- **Regressed by:** `2d0ed4aff59` (`driver_mir_owner_disposition_v1` returns
  `placeholder` for every non-target row of a scoped unit, held HIR included)

## Symptoms (one cause)

```
MIR lowering error: missing provider declaration for imported global 'lib.common.build_manager.contracts::BUILDER_MEMORY_LIMIT_MAX_V2'
MIR lowering error: Result Err record has no exact provider layout at src/lib/nogc_sync_mut/io/file_text_session.spl:100:33
```

The first also surfaced as `ICE[codegen] module
compiler.driver.cache.package_tldr_metadata (attributed): worker died inside
this module`. That attribution is wrong: the worker's own
`[first-compile-error]` names `lib.common.build_manager.codec`.
`lib.nogc_sync_mut.io.external_file` (`FOREIGN_BYTES_LIMIT`) and
`lib.nogc_async_mut.sosix.host_facade` (`SOSIX_TEXT_BYTE_LIMIT`) fail the same
way in the same run.

## Cause

`lower_to_mir_with_target_context` passed `ctx.mir_feed_modules` to
`lower_module` as its provider list. Since `2d0ed4aff59` a scoped unit's feed
holds its targets only, although the unit still holds its imports' HIR (load
closure, or interface-only through the `.hirkey` sidecar). `lower_module`
reads two things from the provider list and nowhere else:

- imported module globals: `register_imported_global_bindings`
  (`50.mir/_MirLowering/provider_globals.spl:127`), then
  `reject_missing_global_providers`;
- class field types under the class identity key: `register_provider_class`
  (`provider_metadata.spl:955`). The struct-name prescan records a class's
  digest and Err layout types but not `struct_field_hir_type`, so
  `checked_result_err_record_owner` (`result_err_record_owner.spl:217`) fails
  its third check.

Structs and free-function call origins come from the prescan over
`ctx.hir_modules`, which is why most modules still compiled.

## Repro (44 s, frozen Stage 2)

Six modules in a scratch git repo under `src/dfx/`: `consts.spl`
(`pub val DFX_LIMIT: i64 = 42`), `errs.spl` (`class DfxError`), `prov.spl`
(`-> Result<[u8], DfxError>`), `usec.spl` (reads `DFX_LIMIT`), `usee.spl`
(`case Err(error): return Err(DfxWrap.Transport(error))`), `main.spl`.

| run | result |
|---|---|
| `--threads 2` (per-file pool) | both errors above; providers logged `import interface-hir hit` |
| `--threads 2`, `SIMPLE_UNIT_TLDR_IMPORTS=0` | both errors (full closure HIR held) |
| `--threads 2`, `SIMPLE_FILE_WORKERS=0` | builds, binary exits 2 (correct) |

`file_text_session.spl` as entry: fails on the pool, builds with
`SIMPLE_FILE_WORKERS=0` (14 objects) and with `--threads 1`.

## Fix

`driver_mir_unit_provider_rows_v1` (`driver_mir_physical_owners.spl`) selects
the held non-target modules; the direct lane hands `lower_module` the feed
plus those rows. The feed, the schedule and the ledger inventory are
unchanged, so a provider is still never lowered or emitted. Log line:
`[mir-setup] unit-declaration-providers targets=<n> held=<m>`.

Spec: `test/01_unit/compiler/driver/mir_physical_owners_spec.spl`
("declaration providers of a module-scoped per-file unit"). The spec was not
run: this host has no full CLI. The selection function was compiled and run
standalone on the frozen Stage 2.

Not verified: the driver change itself (needs a Stage 2 built from it), and
interface-only HIR as a provider for trait impls and provider methods.

## Until Stage 2 is rebuilt

`SIMPLE_FILE_WORKERS=0` (two-pass shards). No source edit helps: 758 non-spec files
under `src/{compiler,lib,app}` import an upper-case module global in a one-line `use`.
