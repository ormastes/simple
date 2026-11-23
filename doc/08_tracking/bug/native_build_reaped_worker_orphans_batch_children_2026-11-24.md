# native-build: a reaped pool worker orphans its batch children

Status: open; defect confirmed by reading the code, no fix landed. Nothing in
this record was executed: a build was running on the host and no runnable
`simple` binary was available, so every statement below is static reasoning
over release source `60fdb93e3a50` (PR #11158).

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

## Why the two candidate fixes are blocked

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
