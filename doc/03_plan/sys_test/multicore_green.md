# Multicore Green System Test Plan

## Current Executable Coverage

- `doc/03_plan/agent_tasks/multicore_green.md` defines the parallel work orders for Go/profile evidence, Simple OS-thread baseline, cooperative green, multicore-green runtime-pool evidence, and SimpleOS green-carrier proof.
- `doc/02_requirements/feature/multicore_green_options.md` and `doc/02_requirements/nfr/multicore_green_options.md` define the requirement choices that still need user selection before final requirements, architecture, and detail design are claimed complete.
- `test/01_unit/lib/nogc_async_mut/multicore_green_spec.spl` checks Pure Simple join/result semantics for multiple value tasks and asserts interpreter inline fallback through `ran_inline_fallback()` / `used_runtime_pool()`.
- `test/01_unit/lib/nogc_async_mut/multicore_green_native.spl` is a native entry-closure smoke for the `rt_pool_*` path and fails if any handle does not report `used_runtime_pool()`.
- `scripts/check/check-cross-language-perf.shs` produces profile evidence for Simple OS thread, Simple cooperative green, Simple multicore green, C pthreads, and Go goroutines. The generated Simple OS-thread native rows use `thread_spawn` fork-join while `thread_spawn_with_args` native ABI is blocked; generated multicore-green workloads fail if runtime-pool acceptance is not proven for every handle.
- `test/05_perf/profile_scripts/profile_report_contract_test.shs` gates the cross-language Markdown report shape and now requires concrete OS-thread, cooperative-green, multicore-green, C pthread, Go goroutine, large-fanout, Go-vs-C fanout stress, RSS, and `used_runtime_pool()` evidence text.
- `test/01_unit/lib/nogc_async_mut/cooperative_green_spec.spl` checks the semantic cooperative-green facade over the existing single-carrier queue.
- `test/01_unit/os/kernel/scheduler/green_worker_spec.spl` checks the SimpleOS scheduler-facing green-worker contract: CPU affinity, spawn CPU choice, wake-affine placement, stealing threshold, and rebalance decisions.
- `test/01_unit/os/kernel/scheduler/green_task_spec.spl` checks the SimpleOS logical green-task lifecycle: spawn records, park, unpark, no-op unpark misuse, completion, and carrier CPU preservation.
- `test/01_unit/os/kernel/scheduler/green_carrier_spec.spl` checks the SimpleOS carrier bridge contract: runnable enqueue, parked/done suppression, wake-affine re-enqueue, bounded green carrier queue mutation, remote SimpleOS reschedule IPI delivery through `smp_send_ipi`, per-CPU green dispatch selection, typed scheduler run intent, and per-CPU execution-state application.
- `test/01_unit/os/kernel/scheduler/scheduler_spec.spl` checks that the real `Scheduler` owns a separate green execution lane, applies green scheduler intent without mutating normal OS current-task state, records rejected green intents, and extends green slots when topology grows.
- `test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl` checks SimpleOS-lane cooperative green semantics: logical work queues on the current carrier, `run_all` drains queued work, and direct value scheduling remains available for profile fanout rows.
- `test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl` checks hosted SimpleOS multicore-green contracts: remote enqueue records a reschedule IPI, green dispatch applies to scheduler-owned multicore execution state, and topology growth extends green execution slots.
- `test/03_system/os/simpleos/feature/simpleos_green_channel_wake_spec.spl` checks scheduler-integrated green-channel wake: send-unpark output is converted into a carrier enqueue, dispatched on the selected CPU, and applied to scheduler-owned green execution state.
- `test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl` is the opt-in live QEMU proof for the SimpleOS green-carrier AP lane. With `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1 --clean`, it builds `examples/09_embedded/simple_os/arch/x86_64/green_carrier_probe_entry.spl`, boots a two-CPU x86_64 guest, requires `[smp] AP reached 64-bit entry`, and requires `[green-carrier-qemu] PASS=true` after dispatching green work onto CPU1 through the freestanding fixed-slot carrier helper.
- `test/05_perf/stress/multicore_green_fanout_spec.spl` checks fanout/fanin checksum parity across Simple OS threads, cooperative green, and multicore green; it also requires multicore-green handles to report whether the runtime pool was used before treating the row as M:N evidence.
- `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl` parses the cross-language profile smoke report and gates numeric Simple OS-thread and multicore-green native rows against Go goroutine and C pthread baselines, proves Go beats C in the isolated large-fanout stress row, and keeps cooperative green classified as non-M:N.
- `test/01_unit/lib/nogc_async_mut/green_channel_spec.spl` checks the pure Simple green-channel contract: empty recv parks a logical green task, send unparks the oldest waiter, FIFO buffering works, and bounded backpressure does not block the carrier worker.

## Blocking Evidence To Track

- SMF cooperative green still has a mutable-global runtime blocker that can segfault before queue execution.
- SMF multicore-green fanout can still segfault in the smoke report; keep it classified separately from native M:N evidence.
- `thread_spawn_with_args` native explicit-argument probes currently segfault with exit 139; native OS-thread profile evidence uses `thread_spawn` until `doc/08_tracking/bug/native_thread_spawn_with_args_abi_2026-06-06.md` is fixed.
- SimpleOS still needs QEMU SMP evidence for full hardware context-switch handoff across APs. The current live QEMU green-carrier proof covers AP startup plus scheduler-visible CPU1 green dispatch, not a final ring/context-switch handoff.
- The interpreter unit spec can pass its example and then hang in `spipe-docgen`; this is a test-runner/docgen issue, not a failed multicore-green assertion.
- The value-index warning currently recommends angle-bracket indexing that fails to parse in expression contexts; tracked in `doc/08_tracking/bug/angle_bracket_index_lint_parse_mismatch_2026-06-06.md`.
