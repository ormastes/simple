# Copy-on-write MIR fork workers (EXPERIMENTAL, `SIMPLE_MIR_FORK_WORKERS=N`)

Status: implemented, opt-in, **not yet executed** (no compiler was rebuilt or
run for this change; see "Unverified").

## Problem

Each MIR shard worker is a fresh process
(`simple run src/app/cli/native_build_worker.spl ... --mir-shard=i/n`, spawned
by `run_mir_shards` -> `run_ledger_shards` in `src/app/cli/native_build_main.spl`).
Every worker re-runs parse, HIR (cache hit), typecheck and mono, and holds
25-29 GB of post-mono state before it lowers one module. The runtime has no
collector, so that state stays resident for the worker's life. Two workers
is the practical limit on a 121 GB host.

## Design

The coordinator never holds post-mono state (it only spawns workers), so the
fork has to happen inside a worker that has reached mono.

1. **Coordinator** (`run_mir_shards_adopting_v1`): when
   `SIMPLE_MIR_FORK_WORKERS=N` (2..64) is set and the lane is not selective,
   force `count=1, parallel=1`: spawn exactly ONE ordinary shard worker
   (`--mir-shard=0/1`, owner `0/1@0`), the *root*. K roots would each fork N
   children and each hold a full post-mono heap.
2. **Fork point**: `aot_compile_mir_shard_v1`
   (`src/compiler/80.driver/driver_aot_pipeline.spl`, right after the
   `queue`/eligibility checks, before `NativeStagedCodegenStateV1.begin`).
   Mono is complete (`driver_orchestration.spl` phase 4 -> phase 5 ->
   `aot_compile`), nothing in this process is shard-specific yet: the shard
   spec is first read inside `lower_to_mir` (`driver_pipeline_lowering.spl`
   claim-cap/inventory block). Resident cohorts and selective MIR never fork.
3. **Children** (`driver_build/native_mir_fork_v1.spl`): child i sets
   `SIMPLE_MIR_SHARD=i/N` and `SIMPLE_MIR_SHARD_OWNER=0/1@0+fork<i>/<N>`
   in-process, clears `SIMPLE_MIR_FORK_WORKERS` (no recursion), and continues
   as an ordinary shard worker: same inventory, claims (cap ceil(n/N)), LPT
   order, per-PASS sidecars, terminals, seal and `.done`. It leaves via
   `_exit` (`rt_fork_child_exit`) after flushing, so no atexit handler or
   allocator teardown walks the shared heap.
4. **Root**: forks in rounds. Each round reaps every live child
   (`process_wait_raw` = `waitpid`) before deciding anything, so the
   unclaimed count it reads is exact, not a race with live siblings. Each
   reaped child's unterminated claims are sealed under that child's owner
   (`CRASH` on signal death, else `FAILED`; legal because it is reaped).
5. **Re-fork of a dead share** (`native_mir_fork_reforkable_v1`): a share is
   re-forked from the root's untouched post-mono heap when its child stopped
   *unfinished* (no `.done`: signal/OOM death, env-install failure, or a
   refused fork), at least one inventory row is still unclaimed (the
   `hir_shard_recovery_can_replace` rule: no relaunch when everything is
   claimed and sealed), the ledger is not BLOCKED, `SIMPLE_COMPILE_FAIL_FAST`
   is not `1`, and the share has used fewer than
   `NATIVE_MIR_FORK_RETRIES_PER_SHARE_V1` (2) retries. At most 3 rounds.
   The replacement keeps the share spec `i/N` (so its own claim cap ceil(n/N)
   covers the dead child's residue) and gets a fresh owner
   `0/1@0+fork<i>/<N>~r<k>`, so the dead attempt's seal cannot touch the
   replacement's claims. A finished child already walked the whole schedule
   and sealed its own failures; it is never re-forked. Rows the dead child
   claimed keep their `CRASH`/`FAILED` terminal: the ledger refuses a second
   claim on any row with a `.claim`, so they are reported, never re-lowered.
6. **Root exit**: when every share finished, or nothing is left unclaimed,
   the root marks its owner done. It exits 1 if any finished child exited
   non-zero or any row was sealed `CRASH`/`FAILED` in any round; a stopped
   child that left nothing unterminated is judged by its replacement. Module
   verdicts stay the ledger's: the coordinator counts every non-PASS terminal.
   When a share was abandoned (retries exhausted, fail-fast, BLOCKED) with
   rows still unclaimed, the root exits 1
   **without** `.done`. The coordinator now reads progress with
   `hir_shard_recovery_owner_tree_progress_v1` (the owner's own claims plus
   every `+fork` child's), so that root is an unfinished owner with
   progress and the existing replacement path applies (a new root
   generation `0/1@<g+1>` re-runs the front end and forks again). If no child
   could be forked in round 0 the root claims nothing and exits 1 done,
   which the coordinator treats as `fallback`.
7. **Identity**: `SIMPLE_MIR_FORK_WORKERS` is excluded from the module object
   environment identity (it only chooses which process emits a module) and
   refused in admitted-epoch compiles, beside the other shard selectors.

## Fork-safety checklist

| Hazard | Finding | Handling |
|---|---|---|
| Threads alive at fork | Codegen is sequential in-process (`driver_aot_native_output.spl` "concurrency=1"); `--threads` only sizes process pools. The only compiler thread spawner (`group_native_thread_capability.spl`) runs inside `compile_to_native`, after the fork point, and joins. | `rt_fork_shared_heap_v1` counts `/proc/self/task` and returns -2 (no fork) unless exactly 1 thread is alive. Non-Linux returns -3. |
| mimalloc | Vendored mimalloc registers no `pthread_atfork`; safe only when single-threaded, which the check above proves. | — |
| stdout/stderr buffers | Duplicate output if unflushed. | `stdout_flush()` before each fork, `fflush(NULL)` inside the primitive, `stdout_flush()` before `_exit`. |
| Existing fork primitive | `rt_fork_child_setup` redirects the child to pipes stored in ONE static slot: a second concurrent child's pipe is never drained and blocks once 64 KiB fills. | New primitive with no redirection; children write to the inherited stdout/stderr. |
| Parent death | Coordinator deadline kills the root. | Child sets `PR_SET_PDEATHSIG=SIGKILL` and re-checks `getppid()`; orphan claims then have no terminal and the coordinator's inventory close fails closed. |
| Ledger fds / locks | Ledger and cache locks (`file_lock`) are taken and released inside single calls; none is held at the fork point. Temp names use live `getpid()`. `build_log.spl` holds no open FILE (no open/append handle). | — |
| Transient-scope state | The child holds exactly what a spawned shard worker holds at this point, so scope state is the same as today. | — |
| Shared writable mmaps | `MAP_SHARED` exists only in generic file-map externs; no use found on the driver's MIR/codegen path. | Residual risk, listed below. |
| atexit handlers | Only set flags. | Children use `_exit` anyway. |
| Secure temp-dir RNG | Seeded once from the parent's pid; siblings inherit one sequence. | Exclusive `mkdir` + EEXIST retry (64 attempts) keeps it correct; contention only. |

## Expected memory (estimate, not measured)

Shared once: the root's post-mono heap, ~25-29 GB. Per child, private pages
are (a) its MIR, post-chain and LLVM working set for ~1/N of the schedule,
and (b) shared pages it dirties. There is no refcounting or collector, so
reads do not dirty pages. Writers to check first: `ctx.mir_modules` and
other ctx dict growth, lazy canonical-ID / interning registries,
`freeze_storage_registry_for_schedule`, any in-place HIR annotation during
lowering, and mimalloc frees of pre-fork blocks. Expected private size per
child: roughly 2-5 GB at N=16, so 16 children total about 27 + 16 x (2-5) =
60-110 GB, inside a 121 GB host. Measure with `Private_Dirty`/`Pss` from
`/proc/<pid>/smaps_rollup`, not RSS, because RSS counts the shared pages in
every child. A cgroup charges a shared page once.

## Unverified / risks

- Nothing was built or executed: the C file passes `cc -fsyntax-only`; the
  `.spl` changes and `test/01_unit/compiler/driver/native_mir_fork_v1_spec.spl`
  have not run.
- `rt_fork_shared_heap_v1` is a new C-only `rt_*` symbol: a reviewed
  exception row was added to `scripts/check/rt_dual_implementation_baseline.txt`
  and the Stage 4 fork provider contract. A prebuilt runtime capsule or
  archive that predates this C change will not define it, so a compiler built
  from this source must link a runtime rebuilt from the same tree.
- The worker runs as `simple run ...native_build_worker.spl`, so the HOST
  `bin/simple` runtime must define `rt_fork_shared_heap_v1`: the knob does
  nothing until a binary built from this tree is deployed. On an older host
  the extern is unbacked (reads as nil/0); the root detects "0 but same pid"
  and declines (claims nothing, coordinator fallback) instead of acting as a
  child. `check-unbacked-extern-ratchet.shs` (nm over the deployed artifact)
  will flag the declaration until that redeploy lands.
- The knob is inert unless MIR sharding is engaged (ad-hoc default, or
  `SIMPLE_MIR_SHARDING=1`), the build is not `--clean`, and the HIR warm
  generation was admitted.
- A dead child's share is now retried (design steps 5-6), but the build
  still fails: claims precede lowering, so a
  child that dies after claiming leaves at least one `CRASH` row, and
  `native_mir_shard_outcome_v1` returns `fail` on any failed module. Re-fork
  lowers the dead child's unclaimed residue so keep-going reports one CRASH
  row instead of a BLOCKED mass; it does not rescue the build. A child that
  dies before its first claim leaves no CRASH row and a re-fork can recover
  it completely.
- A child OOM-killed under memory pressure may die again on re-fork; the
  2-retry cap bounds that. Replacements run after the whole round is reaped
  (exact unclaimed count), so a dead share's residue costs one extra
  share-length of wall time per retry.
- Inventory rows that every finished child skipped (go-to-end exclusions)
  also read as unclaimed. With a dead share present they cause up to two
  cheap re-forks and then a coordinator replacement generation (a full
  front-end rerun) before the inventory close terminalizes them.
- If the coordinator kills the root (deadline), children die by
  `PR_SET_PDEATHSIG` asynchronously and nothing seals their claims; the
  inventory close fails closed (`-1`), as before.
- Every child still repeats the `lower_to_mir` setup before the per-module
  loop (CPU only). A later fork point inside `lower_to_mir`, after the
  shared setup, would also share that work.
