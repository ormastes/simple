# Shard slot pool refill latency grows with live worker count

Date: 2026-10-19
Bug: BUG-SHARD-POOL-REFILL-LATENCY-20261019
Database registration: pending (bug DB reconciliation pending).
Status: source-confirmed design limit of PR #3815; unmeasured.

The slot pool in `run_ledger_shards` (`src/app/cli/native_build_main.spl`) scans live workers in order
and calls `process_wait(pid, SHARD_POOL_POLL_MS)` (200 ms) on each still-running one before moving on.
When nothing has exited, one idle round costs `200 ms x live workers` — up to 16 s at 80 slots — so a
worker that exits just after its turn waits up to that long before its slot is refilled, and its exit
is noticed late. Negligible against multi-minute MIR workers, but wasteful for short HIR/MIR shards and
it scales with the core count the pool exists to use.

Fix direction (not applied): shrink the per-pid quantum with `pids.len()` (e.g. `max(10, 200 / live)`
ms, keeping the round near 200 ms), or add a wait-any primitive (`waitpid(-1)` / `WaitForMultipleObjects`)
to the process runtime and block on all live workers at once.
