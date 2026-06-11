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
- `green_carrier_fixed_spawn_cpu` and `green_carrier_fixed_run_task` provide a freestanding-safe fixed-slot carrier path for live SimpleOS guests. This keeps the public hosted carrier API unchanged while avoiding heap/text state that can stop tiny x86_64 QEMU probes before serial readback.
- The real `Scheduler` now owns a separate green execution lane through `apply_green_scheduler_intent`, so logical green task ids do not collide with normal OS `TaskId` state.
- SMP/AP/IPI support exists under `src/os/kernel/smp/`; `percpu.spl` now updates per-CPU entries through whole-entry replacement so interpreter-mode specs can exercise SMP state changes without indexed-field assignment failures.
- A full scheduler-aware multicore green runtime still needs broader
  fairness/preemption completion. Hosted blocking compensation now has direct
  executable coverage; the remaining scheduler gap is fairness under sustained
  loop load and a host-side yield/preemption contract. The SimpleOS final AP
  ring/user hardware context-switch handoff itself is now closed by the opt-in
  live QEMU marker-triplet lane; the current QEMU proof also covers AP startup
  plus scheduler-visible CPU1 green dispatch.

## Local Evidence

- `doc/03_plan/agent_tasks/multicore_green.md` now maps the active multicore-green lane into parallel agent work orders: Go/profile evidence, Simple OS-thread baseline, cooperative green semantics, multicore-green runtime-pool evidence, and SimpleOS green-carrier proof.
- `doc/02_requirements/feature/multicore_green.md` and `doc/02_requirements/nfr/multicore_green.md` now record the selected Full Go-Like Runtime Roadmap. The earlier option documents were removed after selection so the canonical lane points at final requirements only.
- `doc/04_architecture/runtime/multicore_green.md` and `doc/05_design/multicore_green.md` define preselection architecture/design invariants that remain valid across the named requirement options.
- `scripts/check/check-cross-language-perf.shs` now emits separate rows for OS thread, cooperative green, and multicore-green candidate workloads. Native OS-thread rows use `thread_spawn` fork-join because they are scheduler-baseline rows; `thread_spawn_with_args` native explicit-argument ABI has focused smoke coverage through `scripts/check/check-thread-spawn-with-args-native.shs`.
- `test/05_perf/profile_scripts/profile_report_contract_test.shs` now fails cross-language reports that omit the OS-thread, cooperative-green, multicore-green, C pthread, Go goroutine, large-fanout, Simple-vs-Go-vs-C fanout stress, RSS, Go runtime/scheduler metadata, or `used_runtime_pool()` evidence needed to compare the models honestly. It also parses the stress table and fails when the numeric Go goroutine row is not faster than the C pthread-per-task row.
- `test/01_unit/lib/nogc_async_mut/multicore_green_native.spl` verifies the native entry-closure path joins multiple multicore-green tasks.
- `test/01_unit/lib/nogc_async_mut/multicore_green_spec.spl` verifies the interpreter semantics, but the current `simple test` command can hang in `spipe-docgen` after reporting the passing example.
- `test/01_unit/os/kernel/scheduler/green_worker_spec.spl` verifies the SimpleOS placement and rebalance contract for future green-task carrier workers.
- `test/01_unit/os/kernel/scheduler/green_task_spec.spl` verifies the SimpleOS logical green-task lifecycle for future green-task carrier workers.
- `test/01_unit/os/kernel/scheduler/green_carrier_spec.spl` verifies the SimpleOS bridge contract between logical green tasks, bounded carrier queues, SimpleOS reschedule IPI state, per-CPU green dispatch selection, typed scheduler run intent, and execution-state application.
- `test/01_unit/os/kernel/scheduler/scheduler_spec.spl` verifies that `Scheduler.apply_green_scheduler_intent` persists the green lane separately from normal OS task scheduling and grows green execution slots with topology changes.
- `test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl` verifies the SimpleOS feature-lane cooperative green contract on the current carrier.
- `test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl` verifies hosted SimpleOS multicore-green contracts across SMP IPI, carrier dispatch, scheduler-owned green execution state, and topology growth.
- `test/03_system/os/simpleos/feature/simpleos_green_channel_wake_spec.spl` verifies hosted SimpleOS green-channel wake integration from pure channel send-unpark output through carrier enqueue, dispatch, and scheduler-owned execution-state update.
- 2026-06-11 follow-up: the earlier interpreter-mode runner mismatch for
  minimal green/cooperative assertions is now closed and regression-covered.
  The fix is tracked in `doc/08_tracking/bug/green_thread_spec_runner_mismatch_2026-06-11.md`,
  and hosted SimpleOS cooperative/multicore feature specs are current green
  evidence again.
- `test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl` verifies the opt-in live SimpleOS/QEMU lane. The forced run on 2026-06-06 used `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1 --clean`, built the x86_64 guest probe, observed `[smp] AP reached 64-bit entry`, and observed `[green-carrier-qemu] PASS=true` after CPU1 fixed-slot green dispatch.
- `test/05_perf/stress/multicore_green_fanout_spec.spl` verifies fanout/fanin checksum parity between Simple OS threads, cooperative green, and multicore green while keeping runtime-pool evidence separate from inline fallback.
- `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl` verifies the checked-in Docker contract report numerically: Simple OS-thread and multicore-green native rows must remain within bounded ratios of Go goroutine and C pthread rows, Go must beat one-pthread-per-task C in the isolated large-fanout stress row with `GOMAXPROCS` pinned to `CPU_WORKERS`, and cooperative green must stay classified as current-carrier, non-M:N work.
- 2026-06-11 host-fairness follow-up: the next substantive host lane is no
  longer "add plain yield." The compiler already has reusable resumable-body
  machinery in `src/compiler_rust/compiler/src/mir/generator.rs`,
  `src/compiler_rust/compiler/src/mir/async_sm.rs`, and
  `src/compiler_rust/compiler/src/mir/state_machine_utils.rs`. Hosted
  `multicore_green` fairness work should prefer reusing that dispatcher/resume
  shape or an equivalent compiler-inserted safepoint path through
  `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs`, rather than
  inventing a third unrelated loop-execution model.
- `test/03_system/feature/usage/cooperative_green_smf_function_global_regression_spec.spl` keeps SMF function-valued global/global-array storage covered after the SMF `__module_init` execution fix: both minimal SMF fixtures compile and run successfully, so delayed `green_spawn(fn)` storage is no longer blocked on this path.
- `test/03_system/feature/usage/cooperative_green_compiled_handle_array_blocker_spec.spl` now keeps regression coverage on the direct compiled cooperative-green function-spawn path: interpreter, SMF, and standalone native workloads that store multiple `GreenThreadHandle` values returned from `cooperative_green_spawn(worker)` all pass again, so the profile lane can stay on the real function-spawn surface instead of the older precomputed-result workaround.
- `test/01_unit/lib/nogc_async_mut/green_channel_spec.spl` verifies the pure Simple green-channel park/unpark/backpressure contract needed before scheduler-integrated channel wakeup.
- `test/01_unit/os/kernel/smp/smp_spec.spl` verifies the named SMP accessors, AP registration, online CPU tracking, IPI send/take behavior, and preemption counter behavior used by the green-carrier apply path.
