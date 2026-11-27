# native-build: a reaped pool worker orphans its batch children

Status: fix landed in source, not yet observed in a build. The defect analysis
below is static reasoning over release source `60fdb93e3a50` (PR #11158); see
"Fix" for what was and was not executed.

## Fix (2026-11-24)

Path 2 below, steps 1 and 2. Step 3 (a spec) was not added: no `simple`
binary was available to run one.

- Seed: `rt_child_set_pdeathsig` is registered in
  `interpreter_extern/mod.rs` through a bridge in `bootstrap_runtime.rs` to
  the one C owner (`runtime_process_tree.c`, already compiled into the seed's
  runtime). No Rust twin: the symbol is on the designed C-only allowlist.
- Worker: the three spawn sites go through
  `native_file_worker_spawn_bound_child_v1`, which publishes the worker's pid
  in `SIMPLE_NATIVE_WORKER_CHILD_PARENT_PID` for the duration of the spawn.
- Child: `native_build_child_bind_parent_v1` runs first in
  `run_native_build_worker` and in bootstrap_main's
  `run_native_build_bootstrap`. Only a marked process acts: it clears the
  mark (unset, not emptied: present `SIMPLE_*` keys feed the environment
  fingerprint), arms SIGKILL-on-parent-death, then exits 1 if the published
  pid no longer exists (the worker died before the arm, which sends no
  signal). Process groups are unchanged, so Ctrl-C still reaches everything.

Executed: `cargo check --release --bin simple` and two seed unit tests
(`dispatch_registers_child_pdeathsig`,
`child_pdeathsig_bridge_is_registered_and_reaches_the_c_owner`), both green.
Not executed: any Simple code. No runnable `simple` binary was available, so
the worker/child path has not run and no reaped worker has been observed
taking its child down.

Limits:

- The Simple sources now need a seed built from this change or later. An
  older seed interpreting them fails each marked batch child with "unknown
  extern function".
- macOS and Windows have no arm (`-100000`): children stay unbound there.
- The kernel ties the signal to the worker THREAD that forked, not the
  process. The spawn is a plain call on the thread running the worker loop;
  that this thread lives as long as the process was read, not measured.
- A child killed this way seals none of its claims; the reaped root's
  recovery seal covers its `+fork` tree as it does for fork children.
- The re-check is "published pid still exists", not `getppid() == pid`: no
  engine exposes getppid to Simple. A worker that is dead but not yet reaped
  when the child arms passes the check and that child stays unbound.
- Scope is the process the worker spawns. Under `SIMPLE_BOOTSTRAP_STAGE3=1`
  (the observed self-build) a role child runs the focused capsule in process,
  so that is the heap holder. A role child that instead delegates through
  `run_native_build_worker` launches its real worker with
  `process_run_timeout_live` (`sh` + `setsid`); that worker is in its own
  session and is NOT bound by this change. Whether any pool configuration
  takes that route was not established.
- Tool children (clang, linker) of a killed child are not signalled.

## Symptom

`run_ledger_shards` (`src/app/cli/native_build_main.spl`) reaps a non-HIR pool
worker with `process_kill(pid)` at the deadline/crash reap (`:1456`) and at the
fail-fast cancel (`:1534`). `process_kill` on a plain pid signals only that
process. The worker's own children are spawned with `process_spawn_async` at
three sites:

- `:2090` the `~h<round>` HIR child (`--hir-shard`),
- `:2151` the `+fork-m<round>` MIR batch child (`--mir-shard`),
- `:3307` the per-file unit child (`NativeFileUnitProcessInvokerV1.run_unit`).

`rt_process_spawn_async` (`src/runtime/runtime_legacy_core.c`) neither changes
the process group nor arms a parent-death signal, so these children outlive a
reaped worker and keep their multi-GB heaps outside the pool's commit
accounting. A child that is hung never exits at all.

Observed 2026-11-24 in a 7-hour compiler self-build: owner `3/4@0+fork-m50`
printed `[mir-shard] done ... passed=0` after its parent worker had been reaped
at the 6 h deadline.

## Wrong comment (corrected with this record)

`src/compiler/80.driver/driver_hir_recovery.spl:198-203` said
"PR_SET_PDEATHSIG takes every fork child down with a killed root". That holds
only for `rt_fork_shared_heap_v1` children (`src/runtime/runtime_fork.c`), not
for the `process_spawn_async` children above, which carry the same `+fork`
owner mark. The comment now says so. Comment text only; no behaviour change.

## Why the two candidate fixes were blocked (path 2 has since landed)

1. **Spawn pool workers with `process_spawn_session`** so `process_kill`
   routes to `process_kill_tree`. Rejected:
   - `rt_process_spawn_session` (`src/runtime/runtime_process_tree.c`) calls
     `setsid` and arms no parent-death signal. Today the workers stay in the
     coordinator's process group, so Ctrl-C, `timeout` or a group kill stops
     them. As session leaders they would survive the coordinator and keep
     claiming until the ledger drains: a larger leak than the one being fixed.
   - `rt_process_tree_support` answers unsupported whenever
     `SIMPLE_BOOTSTRAP_SESSION_ID` or `SIMPLE_BOOTSTRAP_SESSION_EXEC` is set,
     so the fix would switch itself off under a managed bootstrap session.
2. **Have the child arm `rt_child_set_pdeathsig` at role entry.** The symbol is
   defined in `runtime_process_tree.c` and listed in
   `src/compiler_rust/common/src/runtime_symbols.rs:942`, but it is not
   registered in the seed's
   `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`. The seed
   interprets `src/app/cli/native_build_main.spl`, where an unregistered extern
   fails with "unknown extern function", so every seed-driven worker would die.

## Proposed path

1. Register `rt_child_set_pdeathsig` in the seed interpreter
   (`interpreter_extern/mod.rs` + `bootstrap_runtime.rs`, next to
   `rt_process_kill_tree`) and build the seed.
2. Arm it best-effort (SIGKILL) at the entry of the three child roles, so an
   unsupported host never fails the child. Process groups stay unchanged, and
   a crashed worker is covered as well as a reaped one.
3. Add one spec `it` for the pure "should arm" predicate.

## Related conclusions from the same review

- HIR pool deadline: left as is. The wall budget is enforced below Simple by
  the owned-process runtime (`wall_budget_ns`, clamped to 1 h in
  `worker_hir_remaining_budget_v1`), so a Simple-side no-progress re-arm
  cannot extend a launched worker.
- TIMEOUT rows: left terminal within a run. A reaped owner with progress
  already gets a replacement for unclaimed rows
  (`hir_shard_recovery_can_replace`), resume requeues non-adoptable rows, and
  in-run requeue of claimed rows is unsafe until this bug is fixed.
