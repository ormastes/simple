# HIR shard workers die together (commit exhaustion); replacements refuse the inventory; --cache-dir ignores scope (2026-10-25)

Status: PARTIAL FIX (scope + inventory diagnostics landed); worker footprint OPEN.

## Evidence (s3-wa, `C:/dev/wt-rel3-new/build/s3-wa`)
- Admission: `[shard] threads=5 (requested 80 ... available=94151876 kB, tree budget=50000000 kB, worker budget=6000000 kB, parent peak=23476 kB)`.
- Generation 0: all 5 workers claimed (11/140/151/141/163 rows, 601 PASS) and then died within one
  log window: two `memory allocation of N bytes failed` (N = 2.3 MB / 1.2 MB) aborts
  (`exit=-1073740791` = 0xC0000409 fast-fail) and three `exit=-1073741819` (0xC0000005).
- Generation 1 (5 replacements): every one failed `HIR frozen inventory publication failed`
  50 ms into phase 3, `claimed=0` -> coordinator wrote `BLOCKED` "incomplete worker or ledger
  publication"; 907 rows closed BLOCKED; build fell back to in-process serial HIR.
- Ledger: `cache/default/frontend/queue-10580-0` (inventory 1513 rows, .lock present, no tmp).

## Root causes
1. **Gen-0 crash = host commit exhaustion, not a code bug in one module.** Every worker
   rebuilds the whole frozen surface set for the closure, so its real commit is far above
   the fixed 6 GB (`SIMPLE_HIR_SHARD_WORKER_KB` default) admission estimate. The admission's
   "parent peak" term is the slim orchestrator's 23 MB, so it never raises the estimate.
   Host commit limit is 136 GB (128 GB RAM + 8 GB pagefile); when it is exhausted *every*
   process's allocations fail at once, which is why all workers die in the same window and
   why the stage4 lane (estimate forced to 1.5 GB, 19 workers, 2935-file closure) saw
   10 x 0xC0000005 (null from failed alloc) with `claimed=0`. RSS-based guards do not see
   commit (private bytes) on Windows.
2. **Gen-1 inventory refusal**: the worker's inventory differs from the published one
   (identity or rows); the old code gave no reason. Now logged as
   `[hir-shard] owner=.. inventory publication failed: <closure identity differs | row count
   differs | row N differs | no published inventory>`; next run pins which.
3. **Cache scope**: `native_build_frontend_cache_dir_arg` hard-coded `<cache-dir>/default/frontend`,
   which also roots the HIR shard ledger, so `SIMPLE_CACHE_SCOPE=s4mir` wrote under `default/`.
   Fixed: uses `SIMPLE_CACHE_SCOPE` (unset -> `default`, unchanged).

## Remaining to get 16-56 parallel workers
- Measure one worker's peak commit (private bytes) on the 1513- and 2935-file closures and
  set the admission estimate from it (or from the previous run's receipt), counting commit
  headroom, not physical RSS.
- Cut per-worker footprint: workers should load only their claimed modules' import closure
  surfaces (P5 `worker_surface_claim_allowed_v1`) instead of the full frozen set.
