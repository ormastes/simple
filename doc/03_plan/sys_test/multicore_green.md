# Multicore Green System Test Plan

## Current Executable Coverage

- `doc/03_plan/agent_tasks/multicore_green.md` defines the parallel work orders for Go/profile evidence, Simple OS-thread baseline, cooperative green, multicore-green runtime-pool evidence, and SimpleOS green-carrier proof.
- `doc/02_requirements/feature/multicore_green.md` and `doc/02_requirements/nfr/multicore_green.md` define the selected Full Go-Like Runtime Roadmap requirements and NFR gates.
- `doc/04_architecture/runtime/multicore_green.md` and `doc/05_design/multicore_green.md` document the selected architecture/design invariants for the host runtime-pool, cooperative green, profile-evidence, and SimpleOS lanes.
- `test/01_unit/lib/nogc_async_mut/multicore_green_spec.spl` checks Pure Simple join/result semantics for multiple value tasks and asserts interpreter inline fallback through `ran_inline_fallback()` / `used_runtime_pool()`.
- `test/01_unit/lib/nogc_async_mut/multicore_green_native.spl` is a native entry-closure smoke for the `rt_pool_*` path and fails if any handle does not report `used_runtime_pool()`.
- `scripts/check/check-cross-language-perf.shs` produces profile evidence for Simple OS thread, Simple cooperative green, Simple multicore green, C pthreads, and Go goroutines. The generated Simple OS-thread native rows use `thread_spawn` fork-join, while `thread_spawn_with_args` stays in focused ABI smoke coverage; generated multicore-green workloads fail if runtime-pool acceptance is not proven for every handle and now print the hosted queue model. Generated Simple CPU workers use literal loop constants so checksum evidence does not depend on the separate SMF/native global-load blocker. For crash-prone native, SMF, or many-thread profile runs, `PROFILE_DOCKER_ISOLATION=1` re-execs this same profile script inside Docker with `--network=none`, UID/GID matching, memory/CPU limits, and the mounted workspace; it is not a separate profile harness. The canonical C/Go toolchain image is `simple-cross-language-perf:latest`, built with `docker build -t simple-cross-language-perf:latest -f tools/docker/Dockerfile.cross-language-perf tools/docker` so Docker sends only the small image context; `simple-test-isolation:latest` remains enough only for Simple-only smoke containment. Auto Docker binary selection now prefers `bin/simple` / `bin/release/simple`; `PROFILE_DOCKER_SIMPLE_BINARY=src/compiler_rust/target/debug/simple` is now only a targeted regression path for the remaining debug-binary linker issue tracked in `doc/08_tracking/bug/docker_cross_language_profile_native_link_2026-06-08.md`. The checked-in current cross-language evidence is `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`, which records the post-fix positive `thread_spawn` native rows and `GOMAXPROCS=CPU_WORKERS` fairness.
- Fresh isolated evidence from
  `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`
  shows the earlier native `thread_spawn` zero-join blocker is closed across
  the host-native and Docker profile lanes. The report now records positive
  `Simple (native)` OS-thread worker and fanout rows again, and the historical
  blocker note in `doc/08_tracking/bug/thread_spawn_native_zero_join_2026-06-11.md`
  is closure tracking rather than an active failure.
- `test/05_perf/profile_scripts/profile_report_contract_test.shs` gates the cross-language Markdown report shape and now requires concrete OS-thread, cooperative-green, multicore-green, C pthread, Go goroutine, large-fanout, Simple-vs-Go-vs-C fanout stress, RSS, Go runtime/scheduler metadata, Docker-isolation metadata, Go `GOMAXPROCS` matching `CPU_WORKERS`, and `used_runtime_pool()` evidence text. It also rejects numbered spawn API names, rejects generated Simple global benchmark constants, fails the report when either the numeric Go stress fanout row or the Simple multicore-green stress fanout row is not faster than the C pthread-per-task stress row, and applies the stronger Simple multicore-green-vs-C fanout comparison to large reports with `Fanout workers:** 1000`.
- `test/05_perf/profile_scripts/profile_report_contract_negative_test.shs` mutates temporary copies of the large profile report so Simple multicore-green fanout, Simple multicore-green stress, and Go stress rows are slower than C pthread rows, mutates Simple multicore-green queue evidence to `queue_model=global_fifo`, pool evidence to a partial `pool_used` count, and hosted parallelism evidence to missing; it expects the profile contract to fail with the matching Go-vs-C, Simple-vs-C, or runtime-pool evidence error.
- `test/03_system/feature/usage/smf_runtime_pool_closure_regression_spec.spl` compiles and runs a minimal SMF wrapper workload equivalent to the generated profile shape `spawn_worker() -> multicore_green_spawn(\: worker())`; it requires the wrapper helper to execute through compiled SMF code, join the runtime-pool handle, and print `wrapper_smf_pool_pass=true`.
- `test/01_unit/lib/nogc_async_mut/cooperative_green_spec.spl` checks the semantic cooperative-green facade over the existing single-carrier queue.
- `test/03_system/feature/usage/cooperative_green_compiled_handle_array_blocker_spec.spl` now keeps regression coverage on the compiled cooperative-green function-spawn path: the interpreter control, SMF path, and standalone native path all pass, so the cross-language/profile lane can use the direct `cooperative_green_spawn` surface again.
- `test/01_unit/os/kernel/scheduler/green_worker_spec.spl` checks the SimpleOS scheduler-facing green-worker contract: CPU affinity, spawn CPU choice, wake-affine placement, stealing threshold, and rebalance decisions.
- `test/01_unit/os/kernel/scheduler/green_task_spec.spl` checks the SimpleOS logical green-task lifecycle: spawn records, park, unpark, no-op unpark misuse, completion, and carrier CPU preservation.
- `test/01_unit/os/kernel/scheduler/green_carrier_spec.spl` checks the SimpleOS carrier bridge contract: runnable enqueue, parked/done suppression, wake-affine re-enqueue, bounded green carrier queue mutation, remote SimpleOS reschedule IPI delivery through `smp_send_ipi`, per-CPU green dispatch selection, typed scheduler run intent, per-CPU execution-state application, scheduler-owned carrier parallelism limits, explicit requested limit preservation, default topology-following limits, active-limit dispatch backpressure, and carrier-queue rebalancing from inactive/overloaded carriers to active carriers.
- `test/01_unit/os/kernel/scheduler/scheduler_green_parallelism_spec.spl` checks that the real `Scheduler` owns the green carrier parallelism state, clamps active carriers to topology, preserves requested carriers across topology changes, keeps default limits aligned to topology growth, runs dispatch on topology-activated carriers, rejects green dispatch on inactive carriers without dropping queued work, uses the scheduler-owned rebalance wrapper to execute rebalanced inactive-carrier work on an active carrier, computes rebalance decisions from live carrier queue depths, runs bounded repeated rebalance passes until inactive queues drain or move budget is exhausted, owns a one-step green carrier run helper that dispatches through the active carrier limit before applying scheduler intent, runs a bounded active-carrier pass across active workers after budgeted rebalance, repeats active passes until no active work remains or the explicit run budget is exhausted, yields the current green task back to the active carrier queue without dropping it, tick-yields a running green task when its scheduler-owned time slice expires, sweeps timer ticks across active carriers without touching inactive carriers, routes the hardware `VEC_TIMER` adapter through green preemption with EOI-required evidence, and routes named runtime/compiler safepoint adapters through the shared preemption bridge.
- `test/01_unit/os/kernel/scheduler/scheduler_green_user_handoff_spec.spl` checks the Pure Simple scheduler boundary between green-carrier dispatch and a real user-task handoff record: a seeded user TCB pid is dispatched through `run_green_carrier_once`, the scheduler-owned green CPU state records that pid, normal OS current-task state remains unchanged, `get_user_handoff_task(pid)` still exposes the matching `user_context`, and the non-entering x86_64 validation boundary accepts that handoff for the later architecture bridge.
- `test/01_unit/os/kernel/arch/x86_64_user_entry_validation_spec.spl` checks the safe syscall-14 validation boundary directly: missing user handoff state is rejected without entering ring-3, while a real x86_64 user image handoff record exposes the expected pid, context, selector frame, and CR3 value.
- `test/01_unit/os/kernel/scheduler/scheduler_spec.spl` checks that the real `Scheduler` owns a separate green execution lane, applies green scheduler intent without mutating normal OS current-task state, records rejected green intents, and extends green slots when topology grows.
- `test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl` checks SimpleOS-lane cooperative green semantics: logical work queues on the current carrier, `run_all` drains queued work, and direct value scheduling remains available for profile fanout rows.
- `test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl` checks hosted SimpleOS multicore-green contracts: remote enqueue records a reschedule IPI, green dispatch applies to scheduler-owned multicore execution state, topology growth extends green execution slots, named runtime/timer/compiler preemption safepoint adapters route through active green carriers, and invalid preemption sources are rejected without ticking carriers.
- `test/03_system/feature/usage/cooperative_green_spec_runner_mismatch_spec.spl`
  keeps regression coverage on the now-closed interpreter-mode runner
  mismatch: the same minimal green-thread queue logic must pass under both
  `simple run` and `simple test`, and hosted SimpleOS cooperative/multicore
  specs are current green-lane evidence again.
- `test/03_system/os/simpleos/feature/simpleos_green_channel_wake_spec.spl` checks scheduler-integrated green-channel wake: send-unpark output is converted into a carrier enqueue, dispatched on the selected CPU, applied to scheduler-owned green execution state, and run through the scheduler-owned active carrier pass after budgeted rebalance.
- `test/03_system/os/simpleos/feature/simpleos_green_hardware_handoff_blocker_spec.spl` keeps the AP ring/user evidence boundaries executable: `SCHED_HANDOFF_PASS=true`, `USER_HANDOFF_READY=true`, `USER_ENTRY_BRIDGE_READY=true`, `USER_SYSCALL_BRIDGE_READY=true`, and `USER_CR3_READY=true` remain prerequisite/readiness evidence, while `HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, and `USER_SYSCALL_PASS=true` are required only from the opt-in final live lane.
- `test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl` is the opt-in live QEMU proof for the SimpleOS green-carrier AP lane. With `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1 --clean`, it builds `examples/09_embedded/simple_os/arch/x86_64/green_carrier_probe_entry.spl` from the `simple-os` submodule, boots a two-CPU x86_64 guest, requires `[smp] AP reached 64-bit entry`, requires `[green-carrier-qemu] PASS=true` after dispatching green work onto CPU1 through the freestanding fixed-slot carrier helper, requires `[green-carrier-qemu] PREEMPT_PASS=true` after the guest runs the fixed timer-preemption helper for the CPU1 green task, requires `[green-carrier-qemu] SCHED_HANDOFF_PASS=true` after the real `Scheduler` dispatches task `701` on CPU1 while leaving the normal OS task slot unchanged, requires `[green-carrier-qemu] USER_HANDOFF_READY=true` after the guest constructs an in-memory user payload image, creates a scheduler user task, dispatches that pid on CPU1's green lane, and validates the non-entering syscall-14 handoff record, requires `[green-carrier-qemu] USER_ENTRY_BRIDGE_READY=true` after the guest installs the x86_64 trap runtime, programs the SYSCALL entry path, and resolves a nonzero `kernel_syscall_entry_asm` address, and requires `[green-carrier-qemu] USER_SYSCALL_BRIDGE_READY=true` after the guest initializes the strong syscall shim keepalive path and dispatches syscall 60 `debug_write` through the kernel-side shim. With `SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1 --clean`, the same spec additionally requires the final AP ring/user marker triplet `HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, and `USER_SYSCALL_PASS=true`.
- `doc/09_report/simpleos_multicore_green_evidence_2026-06-07.md` records the latest SimpleOS verification commands and results for the cooperative, multicore scheduler, green-channel wake, QEMU default, and QEMU live lanes.
- `test/05_perf/stress/multicore_green_fanout_spec.spl` checks fanout/fanin checksum parity across Simple OS threads, cooperative green, and multicore green; it also requires multicore-green handles to report whether the runtime pool was used before treating the row as M:N evidence.
- `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl` parses the Docker contract profile report and gates numeric Simple OS-thread and multicore-green native rows against Go goroutine and C pthread baselines, proves Go beats C in the isolated large-fanout stress row, requires Go `GOMAXPROCS` fairness metadata, and keeps cooperative green classified as non-M:N.
- `test/03_system/feature/usage/concurrency_api_misuse_spec.spl` checks the public concurrency API contract: approved meaningful public names remain usable through `test/05_perf/profile_scripts/concurrency_api_contract_test.shs` with `positive_fixtures=5` and `misuse_fixtures=6`, including `task_spawn`; `task_spawn_wrong_surface_import.spl` and `multicore_green_wrong_surface_import.spl` reject the OS-thread facade; wrong-surface imports, wrong arity, non-closure arguments, bad parallelism argument types, and forbidden numbered aliases fail closed at compile time; and `doc/06_spec/test/03_system/feature/usage/concurrency_api_misuse_spec.md` mirrors the executable manual. The current-source rerun on 2026-06-12 passes all six scenarios but remains perf-sensitive at about 80 seconds because it launches many isolated compiler-check fixtures.
- `test/03_system/feature/usage/multicore_green_agent_plan_spec.spl` checks that `doc/03_plan/agent_tasks/multicore_green.md` uses meaningful parallel-agent lane names instead of `Agent A`/`Agent B` labels, and keeps each lane tied to deliverables and acceptance evidence.
- `test/03_system/feature/usage/multicore_green_fairness_preemption_gap_spec.spl` keeps the remaining hosted fairness/preemption gap explicit: with hosted parallelism pinned to `1`, a tight CPU loop can still monopolize the only worker long enough to keep a later quick task unfinished during the first short observation window on both source-run and standalone native paths.
- `test/03_system/feature/usage/multicore_green_thread_yield_gap_spec.spl` proves that raw `thread_yield()` inside a one-worker hosted multicore-green task still does not let queued work progress during that same first short window, so the remaining host gap is deeper than a missing OS-thread yield primitive.
- `test/03_system/feature/usage/multicore_green_sliced_fairness_regression_spec.spl`
  proves the explicit Pure Simple sliced-task API can provide a hosted
  fairness contract without changing plain closure semantics: with hosted
  parallelism pinned to `1`, `multicore_green_spawn_sliced` requeues a long CPU
  task between short slices, a later quick `multicore_green_spawn` completes
  during the first observation window, and `multicore_green_parallelism()`
  remains `1` on both source-run and standalone native paths. The 2026-06-12
  native compile/run SSpec takes about 60 seconds and remains perf-sensitive.
- `test/03_system/feature/usage/native_struct_array_runtime_blocker_spec.spl`
  now regression-covers the closed smaller hosted-native blocker beneath the
  callback-id resumable-stepper lane: a direct native array of a by-value
  struct is green again on current-source seed/native.
- `test/03_system/feature/usage/multicore_green_handle_array_join_native_blocker_spec.spl`
  now regression-covers the closed hosted-native helper path beneath the
  callback-id resumable-stepper lane: local `MulticoreGreenHandle` array
  iteration plus `join()` now prints `result=7` with `EXIT=0` in the standalone
  native artifact.
- `test/03_system/feature/usage/multicore_green_helper_handles_return_native_blocker_spec.spl`
  now regression-covers the closed helper handle-array return path beneath the
  callback-id resumable-stepper lane: the spec writes real multi-line Simple
  source, type-checks it, compiles it to hosted native, and verifies that a
  helper can join local `MulticoreGreenHandle` values and return a separate
  result array with `after=7` and `EXIT=0`. The 2026-06-12 corrected run is
  functionally green, but this native compile/run SSpec takes about 64 seconds
  and remains perf-sensitive.
- `test/03_system/feature/usage/multicore_green_post_join_array_return_native_blocker_spec.spl`
  now regression-covers the closed post-join array-return blocker: a
  `multicore_green` worker can be joined, followed by post-join `println`
  work, before returning a local result array that prints `result=7` with
  `EXIT=0`. The 2026-06-12 run is functionally green, but this native
  compile/run SSpec still takes about 60 seconds and remains perf-sensitive.
- `doc/08_tracking/bug/multicore_green_release_binary_stale_2026-06-11.md`
  records that the checked-in `bin/release/simple` binary has drifted from the
  current-source rebuilt `release` and `debug` compilers for the
  resumable-stepper native probe. The helper-return probes are now fixed on the
  rebuilt debug path, so rebuilt current-source artifacts remain the stronger
  evidence until the checked-in release binary is refreshed to match current
  source/runtime/compiler behavior.
- `test/03_system/feature/usage/native_function_value_loop_return_regression_spec.spl`
  now regression-covers the closed smaller standalone-native blocker beneath
  the resumable-stepper lane: returning a function value from inside a
  loop/search branch now returns `EXIT=0` in standalone native artifacts.
- `test/01_unit/lib/nogc_async_mut/green_channel_spec.spl` checks the pure Simple green-channel contract: empty recv parks a logical green task, send unparks the oldest waiter, FIFO buffering works, and bounded backpressure does not block the carrier worker.

## Blocking Evidence To Track

- SMF mutable globals are covered by `test/03_system/feature/usage/cooperative_green_smf_mutable_global_regression_spec.spl`; cooperative-green rows remain separate from `multicore_green_spawn` because they are not M:N CPU-parallel evidence.
- `thread_spawn_with_args` native explicit-argument probes are covered by `scripts/check/check-thread-spawn-with-args-native.shs`; native OS-thread profile evidence intentionally stays on `thread_spawn` so the scheduler benchmark measures one-OS-thread-per-spawn fanout separately from explicit-argument ABI smoke coverage.
- Simple multicore-green stress evidence now uses 512 workers with compact handle-array generated workloads; generated many-spawn native compile cost remains a separate scale target in `doc/08_tracking/bug/multicore_green_stress_scale_blockers_2026-06-07.md`.
- SimpleOS final ring/user context-switch handoff across the green-carrier path is now proven by the `SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1` lane and recorded in `doc/09_report/simpleos_multicore_green_evidence_2026-06-07.md`. The default live QEMU green-carrier readiness evidence still covers AP startup, fixed-slot CPU1 green dispatch/IPI evidence, fixed timer-preemption yield evidence, scheduler-owned CPU1 green handoff through `Scheduler.run_green_carrier_once`, user-task handoff readiness through `create_user_task_pid` plus non-entering syscall-14 validation, user-entry bridge readiness through trap runtime plus SYSCALL entry installation, and syscall bridge readiness through the strong debug-write shim. The final live gate must continue to observe `HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, and `USER_SYSCALL_PASS=true` from the real AP ring/user path before docs or reports claim final hardware handoff.
- The interpreter unit spec can pass its example and then hang in `spipe-docgen`; this is a test-runner/docgen issue, not a failed multicore-green assertion.
- The value-index warning currently recommends angle-bracket indexing that fails to parse in expression contexts; tracked in `doc/08_tracking/bug/angle_bracket_index_lint_parse_mismatch_2026-06-06.md`.

## Current Sync Status (2026-06-12)

- This refresh follows the pushed thread-spawn native regression sync
  (`test: keep thread spawn native regression green`) and records the current
  multicore-green lane evidence after rebasing onto the latest `origin/main`.
- Since the earlier `fa7f7ab27554` profile-script hardening sync, the
  multicore-green lane also synced:
  - closure-aligned SimpleOS final AP ring/user handoff wording across
    requirements, research, architecture, design, tracking, and reports;
  - refreshed multicore-green agent-plan current-state text;
  - refreshed Go-vs-Simple research wording so the remaining parity gap is
    explicitly hosted fairness/preemption, not final hardware handoff proof or
    the already-covered blocking-compensation path.
- The workspace remains dirty outside the multicore-green lane because other
  sessions are active in this checkout; future sync work must keep those files
  out of multicore-green commits unless the user explicitly asks for an
  integration commit.
- Current-source rebuilt debug artifacts now pass the scalar/object
  helper-return probes, helper-side handle-array join, channel-struct send,
  callback registry, function-value param-array, inline lambda array literals,
  function-value loop-return, direct struct-array native regressions, and the
  resumable-stepper scheduler path itself. The later post-join array-return
  path is now closed too: post-join string work before returning a local result
  array prints `result=7` with `EXIT=0` in the regression spec and the
  Docker-isolated rerun. Keep this path perf-sensitive because the host native
  compile/run SSpec still takes about 60 seconds.
- Hosted SimpleOS feature specs rerun on 2026-06-12 still pass: cooperative
  green `3`, multicore green `6`, and green-channel wake `4`. The profile
  report contract and numeric cross-language gate also pass against
  `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`.
