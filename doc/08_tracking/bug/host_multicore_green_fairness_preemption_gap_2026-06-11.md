# Host Multicore Green Fairness and Preemption Gap

Date: 2026-06-11
Status: open
Owner: multicore-green lane

## Summary

The hosted `multicore_green_spawn` lane now has real runtime-pool evidence:

- `used_runtime_pool()` and `pool_used=N/N` are enforced in profile rows
- hosted reports require `queue_model=work_stealing`
- Go-vs-C-vs-Simple stress evidence is current

That is enough for bounded CPU-parallel M:N candidate claims, but it is still
not enough for full Go-like scheduler parity on the host runtime.

The remaining host-side gap is the same one called out in the selected
requirements, research, and architecture docs:

- fairness/preemption is not yet proven end to end for hosted multicore green

## Why This Is Still Open

Current hosted multicore-green evidence proves:

- runtime-pool ownership
- bounded parallelism
- work-stealing queue reporting
- fanout/fanin checksum integrity

Current hosted multicore-green evidence does not yet prove:

- long-running CPU work is preempted or yield-forced with a host-side contract
- host fairness semantics comparable to Go's scheduler under sustained loop load

Current hosted fairness/preemption gap coverage now includes:

- `test/03_system/feature/usage/multicore_green_fairness_preemption_gap_spec.spl`
  keeps the remaining host monopolization gap explicit: with hosted
  parallelism pinned to `1`, a tight CPU task still keeps a later quick task
  unfinished through the first short observation window on both source-run and
  standalone native paths
- this is the current executable proof that hosted multicore-green still lacks
  Go-like preemption or an equivalent enforced yield contract

Current hosted blocking-compensation evidence now includes:

- `test/03_system/feature/usage/multicore_green_blocking_compensation_gap_spec.spl`
  keeps the hosted compensation-worker fix covered: with hosted pool
  parallelism pinned to `2`, two sleeping tasks still allow a third quick task
  to complete within the first 30ms window on both source-run and standalone
  native paths
- blocking compensation now has executable hosted coverage; the remaining host
  parity gap is fairness/preemption

Current hosted bounded-parallelism regression coverage also includes:

- `test/03_system/feature/usage/multicore_green_parallelism_bound_gap_spec.spl`
  now keeps the blocking-aware compensation fix pinned: a requested hosted
  parallelism of `2` stays at `2` under pure CPU saturation on both source-run
  and standalone native paths
- bounded parallelism now has executable hosted regression coverage; the
  remaining host parity gap is fairness/preemption, not oversubscription

SimpleOS has scheduler-facing timer/runtime/compiler safepoint coverage for its
green-carrier lane, but that is not the same as proving the hosted runtime-pool
lane has equivalent fairness/preemption guarantees.

## Current Evidence Boundary

Current positive hosted evidence:

- `test/01_unit/lib/nogc_async_mut/multicore_green_spec.spl`
- `test/01_unit/lib/nogc_async_mut/multicore_green_native.spl`
- `test/05_perf/stress/multicore_green_fanout_spec.spl`
- `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl`
- `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`

Current SimpleOS fairness/preemption evidence:

- `test/01_unit/os/kernel/scheduler/scheduler_green_parallelism_spec.spl`
- `test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl`

These do not yet close the hosted-runtime parity claim.

## Exit Criteria

This gap can close only when the hosted multicore-green lane has executable
evidence for:

- fairness/preemption or an equivalent enforced host-side yield contract

That evidence must be tied into the canonical multicore-green feature tracking
and must not rely on SimpleOS-only scheduler proofs.
