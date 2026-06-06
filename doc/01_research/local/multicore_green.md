# Multicore Green Local Research

## Current Simple Surfaces

- OS threads: `std.concurrent.thread.{thread_spawn, thread_spawn_with_args}` in `src/lib/nogc_sync_mut/concurrent/thread.spl` and `src/lib/nogc_async_mut/concurrent/thread.spl`. This is CPU-parallel, but each spawn maps to a platform thread.
- Cooperative green queue: `std.concurrent.cooperative_green.{cooperative_green_spawn, cooperative_green_spawn_value, cooperative_green_run_one, cooperative_green_run_all}` in `src/lib/nogc_async_mut/concurrent/cooperative_green.spl` over `green_thread.spl`. This is lightweight and deterministic, but it runs on the current OS thread only.
- Multicore-green candidate: `std.concurrent.multicore_green.{multicore_green_spawn}` in `src/lib/nogc_async_mut/concurrent/multicore_green.spl`. This is a Pure Simple facade over `rt_pool_submit`, `rt_pool_join`, and `rt_pool_is_done` for bounded CPU-parallel value work.
- Lower-level pool path: `task_spawn` in `src/lib/nogc_async_mut/thread_pool.spl`. It can use `rt_pool_*`, but currently imports the broader OS-thread handle surface. The profile harness uses `multicore_green_spawn` so the benchmark does not pull unrelated `spl_thread_join` codegen.

## SimpleOS Touchpoints

- Scheduler foundations already exist under `src/os/kernel/scheduler/`, including per-CPU run queues, CPU selection, wake/preempt logic, affinity hooks, and context-switch support.
- The scheduler-facing green-worker contract now exists in `src/os/kernel/scheduler/green_worker.spl`, with unit coverage for affinity, spawn CPU choice, wake-affine placement, stealing threshold, and rebalance decisions.
- The logical green-task lifecycle contract now exists in `src/os/kernel/scheduler/green_task.spl`, with unit coverage for spawn records, park/unpark, no-op unpark misuse, completion, and carrier CPU preservation.
- The SimpleOS green-carrier bridge contract now exists in `src/os/kernel/scheduler/green_carrier.spl`, with unit coverage for runnable enqueue, parked/done suppression, wake-affine re-enqueue, bounded green carrier queue mutation, remote reschedule IPI delivery through `smp_send_ipi`, per-CPU dispatch selection, typed `TaskId` scheduler run intent, and per-CPU execution-state application.
- The real `Scheduler` now owns a separate green execution lane through `apply_green_scheduler_intent`, so logical green task ids do not collide with normal OS `TaskId` state.
- SMP/AP/IPI support exists under `src/os/kernel/smp/`; `percpu.spl` now updates per-CPU entries through whole-entry replacement so interpreter-mode specs can exercise SMP state changes without indexed-field assignment failures.
- A full scheduler-aware multicore green runtime still needs hardware context-switch handoff, blocking syscall boundaries, and QEMU proof that work runs across multiple SimpleOS CPUs/APs.

## Local Evidence

- `scripts/check/check-cross-language-perf.shs` now emits separate rows for OS thread, cooperative green, and multicore-green candidate workloads.
- `test/01_unit/lib/nogc_async_mut/multicore_green_native.spl` verifies the native entry-closure path joins multiple multicore-green tasks.
- `test/01_unit/lib/nogc_async_mut/multicore_green_spec.spl` verifies the interpreter semantics, but the current `simple test` command can hang in `spipe-docgen` after reporting the passing example.
- `test/01_unit/os/kernel/scheduler/green_worker_spec.spl` verifies the SimpleOS placement and rebalance contract for future green-task carrier workers.
- `test/01_unit/os/kernel/scheduler/green_task_spec.spl` verifies the SimpleOS logical green-task lifecycle for future green-task carrier workers.
- `test/01_unit/os/kernel/scheduler/green_carrier_spec.spl` verifies the SimpleOS bridge contract between logical green tasks, bounded carrier queues, SimpleOS reschedule IPI state, per-CPU green dispatch selection, typed scheduler run intent, and execution-state application.
- `test/01_unit/os/kernel/scheduler/scheduler_spec.spl` verifies that `Scheduler.apply_green_scheduler_intent` persists the green lane separately from normal OS task scheduling and grows green execution slots with topology changes.
- `test/01_unit/os/kernel/smp/smp_spec.spl` verifies the named SMP accessors, AP registration, online CPU tracking, IPI send/take behavior, and preemption counter behavior used by the green-carrier apply path.
