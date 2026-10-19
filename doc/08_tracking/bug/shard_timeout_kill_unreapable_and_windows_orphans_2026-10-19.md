# Shard worker timeout kill is unreapable on the Rust seed; Windows kill orphans grandchildren

Date: 2026-10-19
Bug: BUG-SHARD-TIMEOUT-KILL-UNREAPABLE-20261019
Database registration: pending (bug DB reconciliation pending).
Status: source-confirmed (pre-existing, not introduced by PR #3815); no executed reproduction.

## 1. Kill then wait always reports "could not be reaped" (Rust seed)

`run_ledger_shards` (`src/app/cli/native_build_main.spl`, the timed-out / still-running branch) calls
`process_kill(pid)` and then `process_wait(pid, 5000)`, and requires a real reap result
(`reaped != -2 and reaped != -1`). On the Rust seed, `rt_process_kill`
(`src/compiler_rust/runtime/src/value/sffi/env_process.rs`, ~:1224) does `SPAWNED_CHILDREN.remove(&pid)`,
kills and waits the child itself, and drops the handle. The follow-up `rt_process_wait` (~:1170) then
finds no entry and returns `-1` ("Not found"). So every timed-out worker leaves
`owner_stopped = false`, sets `all_stopped = false`, and blocks the ledger with
"worker could not be reaped" — even though the child was in fact killed and reaped. The same pattern
appears in the fail-fast cancel loop. Before PR #3815 the path was equally broken; #3815 makes the
timeout fire per worker from spawn, so it is now reachable more precisely, not more often.

Fix direction (not applied): make the contract explicit — either `rt_process_kill` returns the reaped
status / keeps a tombstone that a later `rt_process_wait` reports, or the caller treats a successful
`process_kill` (true = killed and reaped) as the reap. Mirror the choice in the C runtime twin.

## 2. Windows kill terminates only the direct child

On Windows `std::process::Child::kill` is `TerminateProcess` on the worker alone; workers are not
spawned into a Job Object. Grandchildren (clang, lld, nested `simple` workers) survive a timeout or
fail-fast cancel, keep their memory and file handles, and can hold cache/object files the next
generation writes. Fix direction (not applied): spawn shard workers into a Job Object with
`JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE` and terminate the job; POSIX equivalent is a process group + `killpg`.

## Qualification

Source reading only. No timeout was induced; no native build run.
