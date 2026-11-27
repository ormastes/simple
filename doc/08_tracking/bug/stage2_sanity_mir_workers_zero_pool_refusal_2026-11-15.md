# Stage2 sanity smoke: mir_workers=0 makes the per-file worker pool refuse every build (2026-11-15)

**Status:** FIXED (Wave C3, 2026-11-18 — symmetric admission-usable MIR budget scaling in `file_worker_pool_mir_budget_kb_v1`; original 2026-11-15 note preserved below)
**Area:** src/app/cli/file_worker_pool_refusal.spl + stage2 candidate_frontend_smoke harness

## Symptom

At pin 70d542b8ab3 (carries 9cfdcb0c195 shard-count forwarding + 5f80235594b serial
low-memory MIR sharding), every stage2 lane's sanity smoke
(`candidate_frontend_smoke: p2_add-build`) fails:

```
error: per-file worker pool refused (hir_workers=4 mir_workers=0, need >= 2):
not enough free memory for 2 workers. Free memory=69534052 kB, per-worker budget=9000000 kB
```

The memory figure is a red herring (69 GB free, needs 30 GB). The real trigger is
`mir_workers=0`: file_worker_pool_refusal_v1 refuses whenever
`min(hir_count, mir_parallel) <= 1`, and the smoke build's MIR shard count resolves to
0. Setting SIMPLE_MIR_SHARD_COUNT=8 in the lane env did NOT reach the smoke build
(harness resets or does not forward it).

## Workaround (used by the K3 lane, works)

`SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` -- the error text's own sanctioned escape hatch;
routes the smoke build single-process, bypassing the pool admission. Stage2 then
completes and admits normally.

## Proper fix direction

Forward the MIR shard count (or default it to >= 2) inside the candidate_frontend_smoke
build invocation, or make the pool refusal treat mir_workers=0 as "no MIR sharding
requested" and admit on the HIR lane alone when memory allows.

## Resolution (2026-11-18 — Wave C3)

### Actual root cause

`run_file_worker_pool_v1` (`src/app/cli/native_build_main.spl:1844`) derives `mir_parallel`
via `native_build_shard_threads(admit_args, native_build_pool_mir_worker_budget_kb_v1())`,
not `SIMPLE_MIR_SHARD_COUNT`. `native_build_shard_threads` converts any clamped count
`<= 1` into `0` (`mir_workers=0`).

In `src/app/cli/file_worker_pool_refusal.spl`:

- `file_worker_pool_hir_budget_kb_v1` (`:185`) scaled the 9.0 GB (`9000000` kB) per-file
  worker default against `file_worker_pool_live_admission_usable_kb_v1()`, which incorporates
  `SIMPLE_PROCESS_TREE_RSS_CAP_KIB` and `shard_tree_headroom_kib_v1()` via
  `shard_pool_effective_budget_for_v1`, lowering `hir_budget_kb` toward the `6815744` kB
  (6.5 GiB) floor so `hir_workers` admitted `>= 2`.
- `file_worker_pool_mir_budget_kb_v1(modules, true)` (`:224`) instead read
  `file_worker_pool_live_usable_kb_v1()`, which ignored `SIMPLE_PROCESS_TREE_RSS_CAP_KIB`
  and `shard_tree_headroom_kib_v1()`. With 69.5 GB host `MemAvailable` (`69534052` kB),
  `live_usable_kb_v1()` stayed `>= 18000000` kB, leaving `mir_budget_kb` unscaled at
  `9000000` kB, clamping `shard_threads_mem_cap` to `1` -> `mir_workers=0`, and refusing
  with `per-worker budget=9000000 kB`.

### Fix & regression pin

- `src/app/cli/file_worker_pool_refusal.spl` (`file_worker_pool_mir_budget_kb_v1`):
  switched `scale=true` usable input from `file_worker_pool_live_usable_kb_v1()` to
  `file_worker_pool_live_admission_usable_kb_v1()`, matching `file_worker_pool_hir_budget_kb_v1()`.
- Regression spec: `test/01_unit/app/cli/file_worker_pool_scaled_budget_spec.spl`
  (`live per-file MIR budget scales with the same admission usable as HIR`).
