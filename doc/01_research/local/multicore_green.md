# Multicore Green Local Research

## Current Simple Surfaces

- OS threads: `std.concurrent.thread.{thread_spawn, thread_spawn_with_args}` in `src/lib/nogc_sync_mut/concurrent/thread.spl` and `src/lib/nogc_async_mut/concurrent/thread.spl`. This is CPU-parallel, but each spawn maps to a platform thread.
- Cooperative green queue: `std.concurrent.cooperative_green.{cooperative_green_spawn, cooperative_green_spawn_value, cooperative_green_run_one, cooperative_green_run_all}` in `src/lib/nogc_async_mut/concurrent/cooperative_green.spl` over `green_thread.spl`. This is lightweight and deterministic, but it runs on the current OS thread only.
- Multicore-green candidate: `std.concurrent.multicore_green.{multicore_green_spawn}` in `src/lib/nogc_async_mut/concurrent/multicore_green.spl`. This is a Pure Simple facade over `rt_pool_submit`, `rt_pool_join`, and `rt_pool_is_done` for bounded CPU-parallel value work.
- Lower-level pool path: `task_spawn` in `src/lib/nogc_async_mut/thread_pool.spl`. It can use `rt_pool_*`, but currently imports the broader OS-thread handle surface. The profile harness uses `multicore_green_spawn` so the benchmark does not pull unrelated `spl_thread_join` codegen.

## SimpleOS Touchpoints

- Scheduler foundations already exist under `src/os/kernel/scheduler/`, including per-CPU run queues, CPU selection, wake/preempt logic, affinity hooks, and context-switch support.
- SMP/AP/IPI support exists under `src/os/kernel/smp/`.
- A full scheduler-aware multicore green runtime still needs green task records, park/unpark integration, blocking syscall boundaries, and SimpleOS wakeup/IPI hooks.

## Local Evidence

- `scripts/check/check-cross-language-perf.shs` now emits separate rows for OS thread, cooperative green, and multicore-green candidate workloads.
- `test/01_unit/lib/nogc_async_mut/multicore_green_native.spl` verifies the native entry-closure path joins multiple multicore-green tasks.
- `test/01_unit/lib/nogc_async_mut/multicore_green_spec.spl` verifies the interpreter semantics, but the current `simple test` command can hang in `spipe-docgen` after reporting the passing example.
