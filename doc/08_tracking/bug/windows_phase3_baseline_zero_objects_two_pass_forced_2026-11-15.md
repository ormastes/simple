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

### Blocker 3 fix (lane p3unit-20261115, verification-pending)

Root cause, narrowed: the file-scoped route already existed (PM3 TLDR surfaces in
`driver_source_parse_streaming.spl`). The unit child took it only when
`SIMPLE_FRONTEND_CACHE_DIR` was set, and that variable is only set from
`--cache-dir`. The p3new runners pass no `--cache-dir`, so the root was empty.
The child then silently body-parsed its pick's whole import closure.

Fix:

- `run_unit` hands the child `SIMPLE_UNIT_TLDR_ROOT`. It is the frontend cache dir when one is set, otherwise `<hir_queue>/frontend`.
- A unit child that has the route on but no root now fails closed with `FILE-UNIT-E-NO-TLDR-ROOT`. It no longer falls back to the whole closure.

Spec: `test/01_unit/compiler/driver/native_file_unit_frontend_root_spec.spl`.

Still O(closure) per unit, and not fixed here: `worker_admitted_edges_v1` runs an all-seeds preprocess and import scan over the full inventory in every unit, only to order the pick, and phase 1 still reads every `--source` file.

## Tagged workaround for phase-3 runners

- Leave `SIMPLE_FILE_WORKERS` unset.
- Set `SIMPLE_HIR_SHARD_WORKER_KB=8000000` and `SIMPLE_MIR_SHARD_WORKER_KB=8000000`.
- Do not set `SIMPLE_HIR_CACHE=0`.

This gets the per-file pool admitted. It does not get time-to-first-object under 10 s; that needs Blocker 3 fixed.

## Audit (2026-11-18, `file_worker_pool_refusal.spl` + `parser_preprocessor.spl`)

- Audited `src/app/cli/file_worker_pool_refusal.spl` (`file_worker_pool_mir_budget_kb_v1`, `file_worker_pool_phase_price_kb_v1`, `file_worker_pool_mir_default_price_kb_v1`): Blocker 2 is already resolved on `HEAD` (`5911a32cab0c3f0c7bf6440a377e7263487c028e`, via commits `12e08a583d6`, `01f672340c7`, `00394485c58`).
  - When `scale == true` (`shard_mode == false`, per-file worker pool via `native_build_pool_mir_worker_budget_kb_v1`), `file_worker_pool_mir_budget_kb_v1` defaults to `FILE_WORKER_POOL_PER_FILE_WORKER_KB_V1` (`= SHARD_HIR_WORKER_KB_V1 = 9000000` kB = 9 GB), ignores the shard-only host key `worker_mem_mib` (`26624` MiB = `27262976` kB), and scales down toward `FILE_WORKER_POOL_SCALED_FLOOR_KB_V1` (`6815744` kB = 6.5 GiB).
  - When `scale == false` (`shard_mode == true`, two-pass MIR shard mode), it preserves closure-scaled pricing (`file_worker_pool_mir_host_scaled_price_kb_v1` / `SHARD_MIR_WORKER_KB_V1 = 26424115` kB ceiling) pinned by `test/01_unit/compiler/driver/native_build_pool_refusal_spec.spl`.
- Verified `file_worker_pool_refusal.spl` with `simple.exe test --mode=interpreter`:
  - `test/01_unit/compiler/driver/native_build_pool_refusal_spec.spl`: 20/20 passed.
  - `test/01_unit/app/cli/file_worker_pool_host_key_price_spec.spl`: 4/4 passed.
  - `test/01_unit/app/cli/file_worker_pool_per_file_price_spec.spl`: 4/4 passed.
  - `test/01_unit/app/cli/file_worker_pool_address_space_spec.spl`: 17/17 passed.
  - Note: `test/01_unit/app/cli/file_worker_pool_scaled_budget_spec.spl` ran 29/31 (2 pre-existing failures on Windows host where `PROCESSOR_ARCHITECTURE=AMD64` sets `windows_bits=64` even with a nonexistent ELF path).
- `src/app/cli/file_worker_pool_refusal.spl` also uses `@when(arch=...)` (lines 27–39), now covered by the ADR-005 byte-slice fix in `src/compiler/10.frontend/core/parser_preprocessor.spl`.
- Status stays `verification-pending` until a full Windows phase-3 native run (with `native-build` and `SIMPLE_FILE_WORKERS` unset) confirms Blocker 3 + end-to-end `objs > 0` and `first_obj_s <= 10s`.
