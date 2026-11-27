# Stage 2 native-build: codegen worker dies with signal 6 and no diagnostic (2026-11-12)

Status: fix-implemented-verification-pending (`waiting-for:` aarch64 Stage 2 Cranelift repro; prior status: OPEN, 2026-11-12). Severity P1 (the full-CLI closure contains the modules that
triggered it; any `compiler_cli_build` row is exposed, and the failure carries no diagnostic).

## Symptom
Run 15's Stage 2 (`bfe789dd411`, aarch64, cranelift) building the test runner
(`src/app/test_runner_new/main.spl`, matrix phase-C shape: positional entry, `--low-memory
--entry-closure --threads 2`, `SIMPLE_FILE_WORKERS=0`, `SIMPLE_MIR_SHARD_COUNT=8`,
`SIMPLE_NATIVE_BUILD_THREADS=1`) after the receiver of `update_rust_test_database` was typed
`RunnerTestDbCore` (commit `e5947985ef7`, superseded): parse and HIR complete for all 352 modules, MIR is in
progress (`[build] phase=mir done=64` of 352; `[mir] 100/352` shard progress) with zero module
failures when the first staged codegen batch starts, and the worker dies during that interleaved
MIR+codegen stretch — so the panicking unit is either a batch-1 codegen unit or the next MIR
module after `rust_test_runner`:

```
[build] phase=native_compile state=running unit_kind=modules done=0 total=8 ... current=app.test_runner_new...
[NATIVE] codegen: 8 uncached module(s), concurrency=1 (serial lane in this process: backend session owns codegen)
error: native-build worker terminated with signal 6 before producing a binary; NOT a compile failure.
Exit status: 122
```

Reproduced twice (run-15 sha `bfe789dd411` + typed fix, 316 s; release tip `0ceeb3c3421` + typed
fix, 419 s). Max RSS of the parent 4.4 GB; the cgroup cap (30 GiB) was not reached, so this is a
SIGABRT (panic/assert), not an OOM kill.

## What is known
- The typed receiver pulled 17 modules into the runner closure that the standalone runner never
  had: `test_db_core`, `test_db_io`, `test_db_lock`, `test_db_parser`, `test_db_serializer`,
  `string_interner`, `test_stats` (both `nogc_sync_mut` and `nogc_async_mut` twins), plus
  `common.crypto.crc32`, `compression.gzip.crc`, `database.csm_seal`, `common.string_builder`.
- Those modules are NOT the trigger on their own: a 91-module fixture that imports
  `RunnerTestDbCore`, calls `empty()` and `update_test_result(...)` builds and runs
  (`tests=1 suites=1`, rc=0, 220 s) with the same Stage 2 and shape.
- Batch 1 of the aborting build (13 modules) differs from the batches the unfixed build ran
  only by `lib.nogc_sync_mut.io.linux_process_owner` being named as `current`; the unfixed build
  (closure without the 17 modules) ran all its codegen batches. So the extra modules changed the
  codegen of a pre-existing batch (ordering, provider snapshot, layout) rather than failing
  themselves — the trigger module is not identified.
- **No diagnostic is captured.** `cache/diagnostics/native-build-stderr-<pid>-{1,2}.log` are the
  shard workers' stderr and end at the codegen start; the codegen worker's panic text goes
  nowhere. This is the same gap as
  `unknown_call_origin_panics_codegen_worker_2026-11-12.md` (panic kills the worker instead of a
  per-unit error) plus a capture gap: a worker that aborts must leave its stderr tail in the
  diagnostics directory.

## Repro
Fix worktree at `bfe789dd411` with `e5947985ef7` cherry-picked (typed receiver), run 15's Stage 2
as compiler, scratch `s2runner/build_runner2.sh` (phase-C env) with the runner entry — rc=122.
The deletion variant (PR #8510) at the same sha links (rc=0, 707 s, 333 modules).

## Next
1. Rebuild the typed variant with `--threads 1` (in-process route) so the abort lands on the
   main process stderr with the module name.
2. Capture codegen-worker stderr into `diagnostics/` on abnormal exit.
3. Bisect the batch by module once named.

## 2026-11-27 Fix Implemented (`fix-implemented-verification-pending`)
Implemented deterministic abnormal-exit stderr capture, module/batch attribution, and `--threads 1` in-process diagnostic parity across `src/compiler/80.driver/driver_build/**`, `src/compiler/80.driver/driver_mir_shard*`, and `src/compiler/80.driver/driver_aot_pipeline.spl`:
- `src/compiler/80.driver/driver_build/build_outcome.spl`:
  - Extended `build_outcome_signal_of_status` to decode negative `-(128+N)` wait statuses alongside `128+N`.
  - Added shared non-PID deterministic diagnostic helpers: `build_outcome_abnormal_exit_label_v1` (handling SIGABRT `-134`/`134`/`122`/`-6`, SIGSEGV, SIGKILL, SIGTERM, timeout, empty object), `build_outcome_tail_lines_v1`, `build_outcome_diagnostics_dir_v1` (skipping ephemeral `stage_root`/temp paths and defaulting to persistent `.simple/build/diagnostics` outside `stage_root` when env overrides are unset), `build_outcome_write_diag_artifact_v1`, `build_outcome_capture_worker_stderr_v1`, and `build_outcome_unit_attribution_v1`.
- `src/compiler/80.driver/driver_build/native_codegen_pool_v1.spl`:
  - Wired `native_codegen_pool_run_v1` to persist abnormal-exit stderr + module attribution via `native_codegen_diagnostics_dir_v1` into a persistent diagnostics dir outside `stage_root` (never inside `stage_root` or nested `stage_root/ledger`) BEFORE `stage_root` cleanup via `native_codegen_capture_abnormal_stderr_v1`, emit immediate `[codegen-pool] abnormal-exit` + `stderr-tail` lines, and record `abort_label`/`stderr_diag_path`/`stderr_excerpt` via `native_codegen_receipt_encode_with_diag_v1`.
- `src/compiler/80.driver/driver_build/parallel.spl`:
  - Unified `--threads 1` deterministic and batch error accounting in `_record_compile_outcome` with canonical attribution and `diagnostics/` capture, and made `build_supervised` emit unit attribution + `diagnostics/` capture unconditionally on abnormal exit.
- `src/compiler/80.driver/driver_aot_pipeline.spl`, `src/compiler/80.driver/driver_build/native_staged_codegen.spl`, `native_mir_shard.spl`, `native_mir_fork_v1.spl`, `native_file_worker_v1.spl`, and `src/compiler/80.driver/driver_mir_shard_hir_residency_v1.spl`:
  - Wired `native_staged_codegen_batch_attribute_v1` into `CompilerDriver.native_staged_codegen_flush_v1` on staged batch failures, registry rejections, and withheld batches.
  - Added pre-seal in-flight module claim attribution + HIR residency context + `diagnostics/` capture in MIR fork/shard workers (`native_mir_shard_in_flight_modules_v1`, `native_mir_shard_attribute_abort_v1` routed through `native_mir_shard_diagnostic_parity_v1`, `mir_shard_hir_residency_abort_context_v1`), and enriched `mir-shard` early exit receipts with `diagnostics/` capture and `SIMPLE_MIR_SHARDING=0 SIMPLE_NATIVE_BUILD_THREADS=1` rerun parity.
- **waiting-for:** live aarch64 Stage 2 Cranelift `native-build` repro (`--threads 2` and `--threads 1` parity) of `src/app/test_runner_new/main.spl` confirming the aborting module attribution and `diagnostics/` stderr file end-to-end.
