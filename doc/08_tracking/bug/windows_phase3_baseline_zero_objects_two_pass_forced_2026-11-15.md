# Windows phase-3 baseline produced zero objects: two-pass route forced, guard killed it during HIR warm-up

- Status: verification-pending
- Date: 2026-11-15
- Lane: p3base-20261115
- Run analysed: `C:/dev/p3new/s4new` (2026-11-11, 4 attempts). Read-only; nothing was re-run there.

## Symptom

On every attempt the guard reported `first_obj_s=-1 objs=0 killed=True rc=1`. Peak process-tree memory was 20-36 GB, and the guard killed the run after 15-34 minutes.

## What the logs actually show

1. **The build was not stuck in `phase1:load_sources`.** `build.log.err` ends in `phase3:hir:file:*`, with 1765 HIR file starts and 1759 done. That breaks down as 3 HIR shard workers at about 7.6 GB each, each just under its `SIMPLE_HIR_SHARD_WORKER_KB=8000000` cap.
2. **Every shard re-loads and re-parses the entire closure.** The log has 9249 `phase1:load_sources:input` and `phase2:parse:file` events, which is 3 × 3083 files. `SIMPLE_HIR_CACHE=0` was also set.
3. **Who killed it:** `measure_guard.ps1`, killing only its own process tree:
   - Attempts 1 and 2 hit `CapGB=36` (36.06 / 36.1 GB).
   - Attempts 3 and 4 hit the host `commit_free < 25 GB` floor (24.9 / 24.2 GB). That was host pressure from other lanes, not this build's cap.
4. **Root cause of `objs=0`:** every `p3new` runner (`run*.ps1`, `run_p4.ps1`) sets `SIMPLE_FILE_WORKERS="0"`. That explicitly opts out of the default per-file pool (`NATIVE_PER_FILE_PIPELINE_DEFAULT_V1 = "1"`, `native_file_worker_v1.spl:55`; selection at `native_build_main.spl` "DEFAULT per-file worker pool"). The run took the two-pass shard route instead, where HIR warm-up covers the whole closure before any MIR or object is emitted. So `objs=0` before warm-up finishes is by design.
5. **Throughput:** about 1765 HIR files in about 737 s works out to roughly 2.4 files/s across 3 shards, with about 3083 files per shard. Warm-up cannot finish inside the guard's memory and commit envelope. The run never reached MIR.

This route violates the project rules "one process per file (parse->HIR->MIR->obj)" and "first .o within 10 s" by construction. It is not a compiler defect in the per-file lane.

## Fix / workaround

- Phase-3 runners must leave `SIMPLE_FILE_WORKERS` unset (default per-file pool) and must not set `SIMPLE_HIR_CACHE=0`.
- The baseline recipe is in this lane's PR description. Re-measurement results are recorded below.

## Re-measurement (current release/1.0.0 tree, default per-file route)

Binary: a copy of `stage2_new4.exe`, the newest stage2 on the host. It does not contain the string `SIMPLE_NODE_ATTR`, so an ON/OFF diff with it is not meaningful.

Command: the same command as `run_p4.ps1`, run against my own worktree and cache, with `--threads 80`, `SIMPLE_FILE_WORKERS` unset, and `SIMPLE_HIR_CACHE` unset.

### Blocker 2: the pool is refused at the default budget

The run was refused at about 342 s with `objs=0` and `rc=1`:

`per-file worker pool refused (hir_workers=1 mir_workers=0, need >= 2) ... per-worker budget=27262976 kB`

The default MIR price (`SHARD_MIR_WORKER_KB_V1 = 26424115`, `src/app/cli/shard_mem_clamp.spl:360`) is a whole-HIR MIR-shard figure. It is applied to per-file workers too. With 72 GB free and the 24 GiB reserve, it admits only 1 worker, and the pool needs 2. This is already filed as `native_build_default_worker_budget_26gib_refuses_pool_at_49gb_free_2026-11-09` (P3, open).

Workaround: set `SIMPLE_HIR_SHARD_WORKER_KB=8000000` and `SIMPLE_MIR_SHARD_WORKER_KB=8000000`. With these the pool admits 5 workers.

### Blocker 3 (root cause): each per-file unit child rebuilds the whole closure

With the pool admitted, the process tree looked like this:

- 5 `--file-worker=i/5` processes,
- each spawning one `--hir-shard=i/5` unit child (`NativeFileUnitProcessInvokerV1.run_unit`, `src/app/cli/native_build_main.spl` near line 2908),
- each unit child holding a grandchild at about 2.3-2.4 GB.

Each grandchild was CPU-bound: about 570 CPU-seconds in 12 minutes. In that time it wrote no ledger rows and no objects.

The unit child is spawned with the **full** native-build argv: every `--source` root plus `--entry-closure`. It therefore loads and parses the entire closure (3171 selected files) before it lowers its single claimed module. This matches the old two-pass log, where each shard emitted 3083 `phase1:load_sources:input` events and 3083 `phase2:parse:file` events.

Consequences:

- "One process per file" holds only nominally: each per-file process does O(closure) front-end work.
- Time to first object is about ≥ 10-15 minutes instead of ≤ 10 s.
- Total work is O(files × closure).

### Fix direction (not done in this lane)

The unit child must run a file-scoped front end:

- Parse the claimed module plus the dependency *interfaces* it imports, from the published parse/HIR caches (`[parse-closure] reused request=...` shows the closure selection is already shared).
- Do not re-walk and re-parse every `--source` root.

The fix lives in the driver's unit-worker path. It can only be verified with a stage2 rebuilt from source that contains the fix, because driver logic is compiled into the stage binary. That is a seed native-build of the compiler, which costs one more heavy build.

## Tagged workaround for phase-3 runners

- Leave `SIMPLE_FILE_WORKERS` unset.
- Set `SIMPLE_HIR_SHARD_WORKER_KB=8000000` and `SIMPLE_MIR_SHARD_WORKER_KB=8000000`.
- Do not set `SIMPLE_HIR_CACHE=0`.

This gets the per-file pool admitted. It does not get time-to-first-object under 10 s; that needs Blocker 3 fixed.
