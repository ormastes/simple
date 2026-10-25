# Per-file pipeline: phase barriers in sharded native-build (2026-10-25)

Design: `doc/05_design/compiler/incremental_build/true_per_file_pipeline_v1.md` (P3).

## What was barrier-bound

`native_build_focused_capsule_shards_v1` (`src/app/cli/native_build_main.spl`)
ran three whole passes in sequence: parse shards, then a full HIR shard pass
(`run_ledger_shards("hir-shard", ...)`), then a full MIR shard pass, then the
link-only worker. No module could start MIR until every HIR worker of the pass
was reaped and the pass aggregated, and every MIR worker re-ran mono globally.

## What P3 changes (opt-in `SIMPLE_FILE_WORKERS=1`)

- New role `--file-worker=i/n` (`bootstrap_main.spl` dispatch ->
  `run_native_file_worker_v1`). The coordinator runs ONE pool of file workers
  (`run_file_worker_pool_v1`) instead of the HIR pass + MIR pass, admitted at
  min(`native_build_hir_shard_count`, MIR `native_build_shard_threads`), then
  the unchanged link worker over the MIR ledger (`SIMPLE_MIR_SHARD_LINK`).
- Each worker loops: HIR child claims at most `SIMPLE_FILE_WORKER_BATCH`
  (default 1) modules (`SIMPLE_HIR_SHARD_CLAIM_LIMIT`, `driver_hir_cache.spl`
  `hir_shard_begin`), exits; repeat until the HIR ledger is drained. Then MIR
  children with claim cap = batch lower + emit objects into the MIR ledger.
- Receipts (temp+rename): `<hir_queue>/<sha>.receipt` (MONO-PENDING/FAILED,
  hir_start/hir_done) and `<mir_queue>/<sha>.receipt` next to the `.object`
  sidecar (PASS/FAILED, obj_done, object). Coordinator prints
  `[file-worker] receipts=N overlap_proven=<bool>`.
- Helpers + predicate `file_worker_overlap_proven_v1`:
  `src/compiler/80.driver/driver_build/native_file_worker_v1.spl`, spec
  `test/01_unit/compiler/driver/native_file_worker_v1_spec.spl`.
- Default behaviour unchanged when the flag is unset or the pool is not
  admitted (`skip` -> two-pass path); no MIR verdict -> in-process fallback.

## Mono: what was actually done (fail-closed)

Mono is still a GLOBAL pass (`40.mono/monomorphize_integration.spl`). A MIR
child can only be correct with every module's HIR available, so the worker
does NOT run mono over a single module: every HIR-done module is receipted
`MONO-PENDING`, and MIR children start only when every HIR inventory row is a
PASS terminal (`native_file_worker_hir_ledger_state_v1`); a non-PASS row stops
the worker (MIR never admitted). No object is ever emitted from a partial
program. The per-module "template from imports' HIR cache" variant was not
implemented: there is no API to run mono on a subset and tell missing
templates apart from none needed.

## What remains

- **The mono barrier is still there, now inside the pool.** Hence
  `overlap_proven` is expected FALSE on real builds until P4 (module-scoped
  mono). The coordinator-level pass barrier and aggregate are gone.
- Every HIR/MIR child still parses the whole closure (parse cache) and every
  MIR child loads all HIR + runs global mono: per-round cost is high; batch=1
  multiplies it. P5 (TLDR/skeleton surfaces) retires the whole-closure parse.
- `mir_done_ms` is -1: MIR lowering and object emission run inside one child;
  no per-module MIR-done hook was added to `driver_aot_pipeline.spl`.
- HIR and MIR receipts are keyed differently (source path vs canonical MIR
  module name); no path->module map is recorded.
- Not measured: no stage2 run with `SIMPLE_FILE_WORKERS=1` yet; default flip
  waits on that.
