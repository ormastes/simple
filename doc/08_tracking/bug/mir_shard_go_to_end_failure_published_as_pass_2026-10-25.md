# MIR shard child published go-to-end MIR failures as PASS (2026-10-25)

**Status:** fixed in source (takes effect when the Phase 3 compiler rebuilds itself;
the Stage 2 binary has the old driver compiled in).

## Symptom

Phase 3 run-27e (`SIMPLE_MIR_SHARDING=1 SIMPLE_MIR_FORK_WORKERS=16
SIMPLE_MIR_FORK_CHILD_MODULES=40 --go-to-end`): eight fork children each printed
`[go-to-end] MIR: 1 module(s) failed; continuing with 39 lowered module(s)`,
yet each one's `[mir-shard] done` line read `passed=claimed sealed_failed=0`.
The coordinator reported `failed_modules=3` — only the three cranelift codegen
failures (`os.kernel.memory.vmm_*`). The eight MIR failures had no object and
no failure row; seven were then referenced at link and had to be trap-stubbed:

- compiler.frontend._FlatAstBridge.convert_nodes
- lib.nogc_sync_mut.database.pure_sql._PureDatabase.pure_database
- lib.nogc_sync_mut.database.pure_sql._PureDatabase.row_value_helpers
- compiler.driver.cache.bootstrap_library_archive_v1
- lib.nogc_sync_mut.io.retained_file
- plugins.backend_llvm_lib.llvm_lib_globals
- compiler.driver.driver_build.resident_cohort_seal_v1
- compiler.backend.linker.elf.archive_file

The other objectless modules of that run (`sql.types`, `pure_sql.database`,
`retained_file_abi`, `os.posix.errno`) lowered to 0 functions because they are
pure re-export / extern-only files; they are legitimate facades.

## Root cause

`aot_compile_mir_shard_v1` (`src/compiler/80.driver/driver_aot_pipeline.spl`)
decided each claimed module's PASS with

    (outcome_label == "OK" and has_object) or (outcome_label == "" and not has_object)

The second disjunct is the objectless-facade route. A go-to-end MIR failure is
recorded in the child's in-process `GoToEndLedgerV1` and kept out of
`ctx.mir_modules`, so codegen produces no outcome and no object for it — the
same shape. The child published PASS/UNCACHED, the seal found nothing to
fail, and the child's go-to-end ledger (the only record of the failure) died
with the process. No manifest is written on the shard path.

## Fix

- `native_mir_shard_module_passed_v1(outcome_label, has_object, go_to_end_failed)`
  (`driver_build/native_mir_shard.spl`): a module the worker's go-to-end ledger
  excluded never PASSes; the seal turns it FAILED, the coordinator counts it.
- `go_to_end_record_mir_failure_v1` (`driver_pipeline_lowering.spl`) writes one
  ICE receipt row (phase `mir_lower`) per failed module with its first error,
  unless `_driver_mir_ice_continue` already wrote one. The receipt parts are the
  cross-process channel the owner merges.
- `hir_shard_recovery_failed_rows_v1` (`driver_hir_recovery.spl`) and
  `run_ledger_shards` (`src/app/cli/native_build_main.spl`) print
  `[mir-shard] failed module: FAILED <name>` for every non-PASS terminal.

Spec: `test/01_unit/compiler/driver/native_mir_shard_go_to_end_failure_spec.spl`.

## Review notes (non-blocking)

- Fatal MIR diagnostics now appear in the ICE receipt as `kind=caught`, so
  the unsharded summary says "failed with ICE" for them too. Verdict unchanged.
- With `SIMPLE_COMPILE_FAIL_FAST=1` plus go-to-end, a child holding a failed
  module now exits 1, so fork rolling stops. That is the fail-fast contract.
