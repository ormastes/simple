# Stage 2 native-build: codegen worker dies with signal 6 and no diagnostic (2026-11-12)

Status: OPEN (filed, not fixed). Severity P1 (the full-CLI closure contains the modules that
triggered it; any `compiler_cli_build` row is exposed, and the failure carries no diagnostic).

## Symptom
Run 15's Stage 2 (`bfe789dd411`, aarch64, cranelift) building the test runner
(`src/app/test_runner_new/main.spl`, matrix phase-C shape: positional entry, `--low-memory
--entry-closure --threads 2`, `SIMPLE_FILE_WORKERS=0`, `SIMPLE_MIR_SHARD_COUNT=8`,
`SIMPLE_NATIVE_BUILD_THREADS=1`) after the receiver of `update_rust_test_database` was typed
`RunnerTestDbCore` (commit `e5947985ef7`, superseded): parse, HIR and MIR complete for all
352/354 modules with zero module failures, then the first staged codegen batch dies:

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
