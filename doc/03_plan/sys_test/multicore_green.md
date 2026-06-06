# Multicore Green System Test Plan

## Current Executable Coverage

- `test/01_unit/lib/nogc_async_mut/multicore_green_spec.spl` checks Pure Simple join/result semantics for multiple value tasks and asserts interpreter inline fallback through `ran_inline_fallback()` / `used_runtime_pool()`.
- `test/01_unit/lib/nogc_async_mut/multicore_green_native.spl` is a native entry-closure smoke for the `rt_pool_*` path and fails if any handle does not report `used_runtime_pool()`.
- `scripts/check/check-cross-language-perf.shs` produces profile evidence for Simple OS thread, Simple cooperative green, Simple multicore green, C pthreads, and Go goroutines. The generated multicore-green workloads fail if runtime-pool acceptance is not proven for every handle.
- `test/01_unit/lib/nogc_async_mut/cooperative_green_spec.spl` checks the semantic cooperative-green facade over the existing single-carrier queue.

## Required Future SSPEC

- `test/01_unit/lib/nogc_async_mut/green_scheduler_spec.spl`: spawn, yield order, run-one/run-all, join/result, ready count, park/unpark.
- `test/01_unit/lib/nogc_async_mut/green_channel_spec.spl`: channel recv parks, send unparks, bounded backpressure does not block the carrier worker.
- `test/01_unit/os/kernel/scheduler/green_worker_spec.spl`: CPU assignment, wakeup CPU selection, affinity, and stealing/rebalancing decisions.
- `test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl`: SimpleOS smoke for cooperative green semantics.
- `test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl`: QEMU SMP smoke proving work runs across multiple SimpleOS CPUs/APs.
- `test/05_perf/stress/multicore_green_fanout_spec.spl`: fanout/fanin performance versus OS threads, cooperative green, Go goroutines, and C pthreads.

## Blocking Evidence To Track

- SMF cooperative green still has a mutable-global runtime blocker that can segfault before queue execution.
- SMF multicore-green fanout can still segfault in the smoke report; keep it classified separately from native M:N evidence.
- The interpreter unit spec can pass its example and then hang in `spipe-docgen`; this is a test-runner/docgen issue, not a failed multicore-green assertion.
