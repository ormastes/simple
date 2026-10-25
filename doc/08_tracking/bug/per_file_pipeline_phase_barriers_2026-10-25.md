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

## P4 wiring: MIR(F) waits only on F and its imports (opt-in, 2026-10-25)

With `SIMPLE_FILE_WORKERS=1` **and** `SIMPLE_MONO_MODULE_SCOPED=1` the worker
runs `run_native_file_worker_scoped_v1` (`native_build_main.spl`) instead of
the HIR-drain-then-wait loop. Without the mono flag the old behaviour is
unchanged.

- **Barrier removed:** the whole-HIR-ledger wait inside the pool. After every
  HIR round the worker admits MIR(F) for each module it HIR-claimed once
  HIR(F) and HIR of F's **direct** imports are PASS
  (`native_file_worker_deps_ready_v1`). The HIR child writes
  `<hir_queue>/<sha(path)>.deps` (F's direct import source paths, from the
  frozen `ModuleSurface.import_target_indices`) before F's terminal
  (`driver_hir_pipeline_lowering.spl`, streaming shard path).
- **Why direct, not transitive:** module-scoped mono collects templates from
  the modules F imports. A template reachable only through a re-export chain
  shows up as `E-MONO-040`; the MIR child then widens once to the transitive
  closure (deps records) and, if still missing, writes
  `<mir_queue>/<sha(path)>.mono-pending`, fails, and the worker receipts
  `MONO-PENDING` (no object is emitted).
- **MIR child:** `SIMPLE_MIR_SHARD_ONLY_PATHS` (excluded from the native
  environment identity) restricts its claims to the admitted paths
  (`driver_pipeline_lowering.spl`), and `monomorphize_with_policy` takes the
  gated branch `monomorphize_file_worker_scoped_v1` (pure gate
  `mono_module_scoped_selected_v1(env, file_worker_active)`), which runs
  `run_monomorphization_module_scoped_v1` per admitted module and skips the
  global `process_modules`. Post-mono verify runs over the admitted modules
  only.
- **Receipts:** `deps_ready_ms` added (optional when parsing; older receipts
  still parse), `mir_done_ms` filled from a `.mir-done` stamp the MIR child
  writes when `lower_to_mir` returns. HIR receipts are published for PASS
  modules too, so `file_worker_overlap_proven_v1` can see another module's
  `hir_start` (proven on a 2-module fixture in
  `test/01_unit/compiler/driver/native_file_worker_module_mono_spec.spl`).
- A module without a deps record (non-streaming HIR lane) falls back to the
  whole-ledger gate for that module only.

### Still remaining

- **P5:** every HIR/MIR child still parses the whole closure, and the MIR
  child still loads (or, on a cache miss, lowers) every module's HIR, not
  just F + imports. Templates come from that already-loaded HIR (which was
  read from the HIR cache), not from a separate `hir_cache_load` per import.
- **P4b:** instance bodies placed in F may still reference template-module
  local SymbolIds (non-generic helpers, globals of T); only leaf templates are
  safe until symbol relocation lands.
- Cranelift / non-LLVM backends ignore `is_comdat`.
- UNRUN: the spec fails on this Windows host before execution with
  `parse: in ...\windows_redirected_process.spl: Unexpected token: expected
  Fn, found Colon`. No stage2 run with both flags yet.
