# Multicore Green System Test Plan

## Current Executable Coverage

- `doc/03_plan/agent_tasks/multicore_green.md` defines the parallel work orders for Go/profile evidence, Simple OS-thread baseline, cooperative green, multicore-green runtime-pool evidence, and SimpleOS green-carrier proof.
- `doc/02_requirements/feature/multicore_green.md` and `doc/02_requirements/nfr/multicore_green.md` define the selected Full Go-Like Runtime Roadmap requirements and NFR gates.
- `doc/04_architecture/runtime/multicore_green.md` and `doc/05_design/multicore_green.md` document the selected architecture/design invariants for the host runtime-pool, cooperative green, profile-evidence, and SimpleOS lanes.
- `test/01_unit/lib/nogc_async_mut/multicore_green_spec.spl` checks Pure Simple join/result semantics for multiple value tasks and asserts interpreter inline fallback through `ran_inline_fallback()` / `used_runtime_pool()` on both value and sliced handles.
- `test/01_unit/lib/nogc_async_mut/multicore_green_native.spl` is a native entry-closure smoke for the `rt_pool_*` path and fails if any handle does not report `used_runtime_pool()` or if submitted/completed/pending/busy/blocked public counter evidence is inconsistent after join.
- `scripts/check/check-cross-language-perf.shs` produces profile evidence for Simple OS thread, Simple cooperative green, Simple multicore green, C pthreads, and Go goroutines. The generated Simple OS-thread native rows use `thread_spawn` fork-join, while `thread_spawn_with_args` stays in focused ABI smoke coverage; generated multicore-green workloads fail if runtime-pool acceptance is not proven for every handle and now print hosted queue model plus public counter-delta evidence. Generated multicore-green profile code must store `MulticoreGreenHandle` values and call public `handle.join()`; it must not import `rt_pool_join` directly now that the handle-array native blocker is closed. The report also contains a separate `Hosted Fairness Evidence` section for `multicore_green_spawn_sliced` quick-task progress and ordinary `multicore_green_spawn` loop-safepoint fairness. Source rows are interpreter-inline semantic checks; native rows require `used_runtime_pool=true`, so inline fallback cannot pass as M:N hosted fairness. Generated Simple CPU workers use literal loop constants so checksum evidence does not depend on the separate SMF/native global-load blocker. For crash-prone native, SMF, or many-thread profile runs, `PROFILE_DOCKER_ISOLATION=1` re-execs this same profile script inside Docker with `--network=none`, UID/GID matching, memory/CPU limits, and the mounted workspace; it is not a separate profile harness. The canonical C/Go toolchain image is `simple-cross-language-perf:latest`, built with `docker build -t simple-cross-language-perf:latest -f tools/docker/Dockerfile.cross-language-perf tools/docker` so Docker sends only the small image context; `simple-test-isolation:latest` remains enough only for Simple-only smoke containment. Auto Docker binary selection now probes candidates with `--version`, prefers runnable `bin/simple` / `bin/release/simple`, and skips a stale release wrapper whose wrapped platform binary is missing; `PROFILE_DOCKER_SIMPLE_BINARY=src/compiler_rust/target/debug/simple` is now only a targeted regression path for the remaining debug-binary linker issue tracked in `doc/08_tracking/bug/docker_cross_language_profile_native_link_2026-06-08.md`. The checked-in current cross-language evidence is `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`, which records the post-fix positive `thread_spawn` native rows, `GOMAXPROCS=CPU_WORKERS`, hosted sliced-fairness evidence, and hosted loop-safepoint fairness evidence.
- Fresh isolated evidence from
  `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`
  shows the earlier native `thread_spawn` zero-join blocker is closed across
  the host-native and Docker profile lanes. The report now records positive
  `Simple (native)` OS-thread worker and fanout rows again, and the historical
  blocker note in `doc/08_tracking/bug/thread_spawn_native_zero_join_2026-06-11.md`
  is closure tracking rather than an active failure.
- `test/05_perf/profile_scripts/profile_report_contract_test.shs` gates the cross-language Markdown report shape and now requires concrete OS-thread, cooperative-green, multicore-green, hosted sliced-fairness, hosted loop-safepoint fairness, C pthread, Go goroutine, large-fanout, Simple-vs-Go-vs-C fanout stress, RSS, Go runtime/scheduler metadata, Docker-isolation metadata, Docker CPU quota wording as containment metadata rather than scheduler-width proof, Go `GOMAXPROCS` matching `CPU_WORKERS`, the Pure Simple `multicore_green_spawn` facade over runtime-seed `rt_pool_*` wording, `used_runtime_pool()` evidence text, and public counter-delta evidence. With no arguments it is the canonical existing profile-contract check for `scripts/check/check-cross-language-perf.shs` and `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`; it also checks `doc/09_report/README.md` and `doc/03_plan/agent_tasks/multicore_green.md`, printing `report_index_checked=doc/09_report/README.md` and `agent_task_plan_checked=doc/03_plan/agent_tasks/multicore_green.md` so the report index, SimpleOS evidence row, and agent handoff cannot silently point future agents at stale evidence. Pass explicit arguments only when validating another profile/report pair. It rejects missing cooperative-green rows; cooperative-green rows that claim M:N, goroutine, runtime-pool, `pool_used=`, `parallelism=`, counter, or `queue_model=` evidence; stale combined `multicore_green_spawn`/`rt_pool_*` Pure Simple API wording; and multicore-green rows whose `pool_used` count is zero, partial, or otherwise unequal. It also rejects forbidden number-suffix API names across OS-thread, task-pool, cooperative-green, low-level green, and multicore-green surfaces; rejects generated Simple global benchmark constants; fails the report when either the numeric Go fanout row, Go stress fanout row, or Simple multicore-green stress fanout row is not faster than the matching C pthread-per-task row; and applies the stronger Simple multicore-green-vs-C fanout comparison to large reports with `Fanout workers:** 1000`.
- `test/05_perf/profile_scripts/profile_binary_autoselect_test.shs` runs a reduced cross-language profile, computes the expected auto-selected Simple binary by probing candidates with `--version`, and fails if the report selects an executable but stale release wrapper instead of the first runnable candidate.
- `test/05_perf/profile_scripts/profile_help_contract_test.shs` verifies `scripts/check/check-cross-language-perf.shs --help` prints usage and exits before workload compilation, so agents can inspect the profile harness without accidentally starting a long benchmark.
- `test/05_perf/profile_scripts/profile_docker_isolation_contract_test.shs` stubs Docker and verifies `PROFILE_DOCKER_ISOLATION=1` re-execs the same profile script through `docker run` with `--network=none`, memory and CPU limits, UID/GID mapping, workspace mount, and full profile environment handoff for run counts, worker counts, fanout counts, warm-process counts, timeout, and `GOMAXPROCS`, so crash-prone native/SMF profile runs stay in a separate process/container boundary without silently dropping tuning knobs.
- `test/02_integration/simple_wrapper_runtime_probe_test.shs` keeps user-facing wrappers aligned with the same stale-release rule: `bin/sj` and `bin/simple-interp` must skip an executable wrapper whose platform target is missing and use the first candidate that passes `--version`.
- `test/05_perf/profile_scripts/profile_report_contract_negative_test.shs` mutates temporary copies of the large profile report so Simple multicore-green fanout, Go fanout, Simple multicore-green stress, and Go stress rows are slower than C pthread rows, removes required Simple multicore-green worker rows into the `simple_multicore_worker_rows_missing` failure case, removes the Simple multicore-green SMF fanout row into the `simple_multicore_smf_fanout_row_missing` failure case, mutates Simple multicore-green queue evidence to `queue_model=global_fifo`, pool evidence to a partial `pool_used` count, pool evidence to the `simple_multicore_pool_used_zero` failure case, hosted parallelism evidence to missing, public counter evidence to missing, hosted fairness section evidence to missing, hosted sliced-fairness markers to false, hosted loop-safepoint markers out of the report, the hosted sliced-fairness explanation away from the explicit scalar-state contract, the Pure Simple/runtime-seed wording into the `pure_simple_runtime_seed_boundary_corrupt` failure case, the cooperative-green explanation away from `not a Go M:N goroutine equivalent`, a cooperative-green row into the `cooperative_green_mn_runtime_pool_label` failure case, cooperative-green current-thread wording into the `cooperative_green_current_thread_wording_missing` failure case, cooperative-green rows out of the report into the `cooperative_green_profile_row_missing` failure case, an OS-thread row into the `os_thread_profile_row_thread_spawn_with_args` failure case, an OS-thread row out of the required section into the `os_thread_profile_row_missing` failure case, an OS-thread timing into the `os_thread_profile_timing_fail` failure case, Docker Simple binary probe/stale-wrapper wording into the `docker_simple_binary_probe_wording_corrupt` failure case, workload-variety methodology into the `workload_variety_methodology_missing` failure case, optional-language inventory wording into the `optional_language_inventory_missing` failure case, Docker CPU quota/scheduler-width wording into the `docker_cpu_quota_scheduler_width_missing` failure case, the SimpleOS report-index row into the `simpleos_report_index_row_missing` failure case, hosted fairness report-index wording into the `hosted_sliced_fairness_report_index_marker_missing` failure case, and a forbidden number-suffix API name into the `forbidden_number_suffix_api_name` failure case; it expects the profile contract to fail with the matching Go-vs-C, Simple-vs-C, OS-thread-label, OS-thread-presence, OS-thread-timing, runtime-pool, row-presence, Pure-Simple-boundary, cooperative-label, cooperative-presence, cooperative-current-thread, cooperative-explanation, Docker-binary-probe, workload-variety, optional-language inventory, Docker CPU quota/scheduler-width, loop-safepoint fairness, SimpleOS-report-index, hosted-fairness report-index, forbidden-name, counter-evidence, or hosted-fairness evidence error.
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
- `test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl` is the opt-in live QEMU proof for the SimpleOS green-carrier AP lane. With `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1 --clean`, it builds `examples/09_embedded/simple_os/arch/x86_64/green_carrier_probe_entry.spl` from the `simple-os` submodule, boots a two-CPU x86_64 guest, requires `[smp] AP reached 64-bit entry`, requires `[green-carrier-qemu] PASS=true` after dispatching green work onto CPU1 through the freestanding fixed-slot carrier helper, requires `[green-carrier-qemu] PREEMPT_PASS=true` after the guest runs the fixed timer-preemption helper for the CPU1 green task, requires `[green-carrier-qemu] SCHED_HANDOFF_PASS=true` after the real `Scheduler` dispatches task `701` on CPU1 while leaving the normal OS task slot unchanged, requires `[green-carrier-qemu] USER_HANDOFF_READY=true` after the guest constructs an in-memory user payload image, creates a scheduler user task, dispatches that pid on CPU1's green lane, and validates the non-entering syscall-14 handoff record, requires `[green-carrier-qemu] USER_ENTRY_BRIDGE_READY=true` after the guest installs the x86_64 trap runtime, programs the SYSCALL entry path, and resolves a nonzero `kernel_syscall_entry_asm` address, requires `[green-carrier-qemu] USER_SYSCALL_BRIDGE_READY=true` after the guest initializes the strong syscall shim keepalive path and dispatches syscall 60 `debug_write` through the kernel-side shim, and rejects the final `HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, and `USER_SYSCALL_PASS=true` markers in the scheduler-only live lane. With `SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1 --clean`, the same spec additionally requires the final AP ring/user marker triplet.
- `doc/09_report/simpleos_multicore_green_evidence_2026-06-07.md` records the latest SimpleOS verification commands and results for the cooperative, multicore scheduler, green-channel wake, QEMU default, and QEMU live lanes; its 2026-06-14 interpreter-run refresh reran the cooperative, multicore scheduler, green-channel wake, and final handoff blocker feature specs without changing the opt-in live-QEMU claims.
- `test/05_perf/stress/multicore_green_fanout_spec.spl` checks fanout/fanin checksum parity across Simple OS threads, cooperative green, and multicore green; it also requires multicore-green handles to report whether the runtime pool was used before treating the row as M:N evidence.
- `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl` parses the Docker contract profile report and gates numeric Simple OS-thread and multicore-green native rows against Go goroutine and C pthread baselines, proves Go beats C in the isolated large-fanout stress row, requires Go `GOMAXPROCS` fairness metadata, and keeps cooperative green classified as non-M:N.
- `test/03_system/feature/usage/concurrency_api_misuse_spec.spl` checks the public concurrency API contract: approved meaningful public names remain usable through `test/05_perf/profile_scripts/concurrency_api_contract_test.shs` with `positive_fixtures=6`, generated profile-script contract `misuse_fixtures=11`, checked-in fixture contract `checked_in_misuse_fixtures=29`, and total shell-enforced `total_misuse_fixtures=40`, including `task_spawn` and a run/join proof that `multicore_green_spawn_sliced` returns `public_multicore_green_sliced_result=19 used_runtime_pool=true`; the checked-in `number_suffix_alias.spl` fixture family rejects numbered API aliases with `E-PAR-002` for the `thread_spawn`, `spawn_isolated`, and `spawn_limited` surfaces; `thread_spawn_with_args_wrong_surface_import.spl`, `task_spawn_wrong_surface_import.spl`, `multicore_green_wrong_surface_import.spl`, and `multicore_green_sliced_wrong_surface_import.spl` reject the wrong public facade; wrong-surface imports, wrong arity, non-closure/non-function arguments, bad parallelism or sliced-state argument types, direct runtime aliases including runtime-pool counters, and shared mutable captures in green-process closures fail closed at compile time; the spec verifies the Pure Simple lint source is the authoritative rule map and names Rust checks as seed compatibility; and `doc/06_spec/03_system/feature/usage/concurrency_api_misuse_spec.md` mirrors the executable manual. The current-source rerun on 2026-06-14 passes seven scenarios with `misuse_fixtures=11`, checked-in misuse fixture inventory `checked_in_misuse_fixtures=29`, total shell-enforced `total_misuse_fixtures=40`, and the native `public_multicore_green_sliced_result=19 used_runtime_pool=true` proof after the runtime-pool resolver learned the `rt_pool_*` counter symbols.
- `test/03_system/feature/usage/multicore_green_agent_plan_spec.spl` checks that `doc/03_plan/agent_tasks/multicore_green.md` uses meaningful parallel-agent lane names instead of `Agent A`/`Agent B` labels, and keeps each lane tied to deliverables and acceptance evidence.
- `test/03_system/feature/usage/multicore_green_fairness_preemption_gap_spec.spl` now regression-covers ordinary loop-body fairness: with hosted parallelism starting at `1`, a tight CPU loop reaches compiler-inserted runtime-pool safepoints and a later quick task finishes during the first short observation window on both source-run and standalone native paths.
- `test/03_system/feature/usage/multicore_green_thread_yield_gap_spec.spl` now regression-covers the same compiler/runtime safepoint path when user code also calls raw `thread_yield()`, keeping fairness attributed to runtime-pool safepoints rather than bare OS-thread yielding.
- `test/03_system/feature/usage/multicore_green_safepoint_fairness_regression_spec.spl`
  proves the new explicit runtime-pool safepoint hook makes queued work
  progress on standalone native with hosted parallelism pinned to `1`: a long
  worker that calls `multicore_green_safepoint()` lets a later quick task
  finish during the first observation window, returns the original slow-task
  value, and records compensation capacity by observing
  `multicore_green_parallelism() == 2` after join. This remains the explicit
  user-visible safepoint API beneath the compiler-inserted loop poll path.
- `test/03_system/feature/usage/multicore_green_parallelism_bound_gap_spec.spl`
  proves source-run and standalone native hosted pool width remains bounded and
  that non-positive `multicore_green_set_parallelism` requests clamp to `1`
  before the fixture sets the positive width used by CPU saturation work.
- `test/03_system/feature/usage/multicore_green_sliced_fairness_regression_spec.spl`
  proves the supported hosted fairness contract for CPU-heavy work without
  changing plain closure semantics: with hosted parallelism pinned to `1`,
  `multicore_green_spawn_sliced` enters the runtime pool and requeues a long CPU task between short slices,
  a later quick `multicore_green_spawn` completes during the first observation
  window, and `multicore_green_parallelism()` remains `1` on both source-run
  and standalone native paths. The 2026-06-12 native compile/run SSpec takes
  about 60 seconds and remains perf-sensitive.
- `test/03_system/feature/usage/native_struct_array_runtime_blocker_spec.spl`
  regression-covers the smaller hosted-native by-value struct-array path
  beneath the callback-id resumable-stepper lane on current-source seed/native.
- `test/03_system/feature/usage/multicore_green_handle_array_join_native_blocker_spec.spl`
  regression-covers the hosted-native helper path beneath the callback-id
  resumable-stepper lane: local `MulticoreGreenHandle` array iteration plus
  `join()` must stay explicit evidence instead of being inferred from source
  shape alone.
- `test/03_system/feature/usage/multicore_green_helper_handles_return_native_blocker_spec.spl`
  regression-covers the helper handle-array return path beneath the callback-id
  resumable-stepper lane with real multi-line Simple source, type-check,
  hosted-native compile, and run evidence. This native compile/run SSpec is
  perf-sensitive.
- `test/03_system/feature/usage/multicore_green_post_join_array_return_native_blocker_spec.spl`
  regression-covers the post-join array-return path: a `multicore_green`
  worker is joined before post-join work and local result-array return. This
  native compile/run SSpec remains perf-sensitive.
- `doc/08_tracking/bug/multicore_green_release_binary_stale_2026-06-11.md`
  records that `bin/release/simple` is a probe-required wrapper over an ignored,
  generated platform binary. `scripts/bootstrap/bootstrap-from-scratch.sh
  --deploy` materializes `bin/release/<platform>/simple`; current-source debug
  native regression specs are the stronger evidence unless the wrapper's
  platform delegate exists and passes `--version`.
- `test/03_system/feature/usage/native_function_value_loop_return_regression_spec.spl`
  regression-covers the standalone-native function-value loop-return path
  beneath the resumable-stepper lane.
- `test/01_unit/lib/nogc_async_mut/green_channel_spec.spl` checks the pure Simple green-channel contract: empty recv parks a logical green task, send unparks the oldest waiter, FIFO buffering works, and bounded backpressure does not block the carrier worker.

## Blocking Evidence To Track

- SMF mutable globals are covered by `test/03_system/feature/usage/cooperative_green_smf_mutable_global_regression_spec.spl`; cooperative-green rows remain separate from `multicore_green_spawn` because they are not M:N CPU-parallel evidence.
- `thread_spawn_with_args` native explicit-argument probes are covered by `scripts/check/check-thread-spawn-with-args-native.shs`; native OS-thread profile evidence intentionally stays on `thread_spawn` so the scheduler benchmark measures one-OS-thread-per-spawn fanout separately from explicit-argument ABI smoke coverage.
- Simple multicore-green stress evidence now uses 512 workers with compact handle-array generated workloads; generated many-spawn native compile cost remains a separate scale target in `doc/08_tracking/bug/multicore_green_stress_scale_blockers_2026-06-07.md`.
- SimpleOS final ring/user context-switch handoff across the green-carrier path is now proven by the `SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1` lane and recorded in `doc/09_report/simpleos_multicore_green_evidence_2026-06-07.md`. The default live QEMU green-carrier readiness evidence still covers AP startup, fixed-slot CPU1 green dispatch/IPI evidence, fixed timer-preemption yield evidence, scheduler-owned CPU1 green handoff through `Scheduler.run_green_carrier_once`, user-task handoff readiness through `create_user_task_pid` plus non-entering syscall-14 validation, user-entry bridge readiness through trap runtime plus SYSCALL entry installation, and syscall bridge readiness through the strong debug-write shim. The final live gate must continue to observe `HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, and `USER_SYSCALL_PASS=true` from the real AP ring/user path before docs or reports claim final hardware handoff.
- The interpreter unit spec can pass its example and then hang in `spipe-docgen`; this is a test-runner/docgen issue, not a failed multicore-green assertion.
- The value-index warning currently recommends angle-bracket indexing that fails to parse in expression contexts; tracked in `doc/08_tracking/bug/angle_bracket_index_lint_parse_mismatch_2026-06-06.md`.

## Current Sync Status (2026-06-13)

- This refresh follows the pushed thread-spawn native regression sync
  (`test: keep thread spawn native regression green`) and records the current
  multicore-green lane evidence after rebasing onto the latest `origin/main`.
- Since the earlier `fa7f7ab27554` profile-script hardening sync, the
  multicore-green lane also synced:
  - closure-aligned SimpleOS final AP ring/user handoff wording across
    requirements, research, architecture, design, tracking, and reports;
  - refreshed multicore-green agent-plan current-state text;
  - refreshed Go-vs-Simple research wording so ordinary-closure preemption
    remains future host work while the supported hosted fairness contract is
    the explicit sliced API, not final hardware handoff proof or the
    already-covered blocking-compensation path.
- The shared default checkout remains dirty outside the multicore-green lane
  because other sessions are active; this lane uses a separate jj workspace and
  must keep those files out of multicore-green commits unless the user
  explicitly asks for an integration commit.
- Current-source rebuilt debug artifacts remain the stronger evidence for
  native resumable-stepper and helper-return probes until the checked-in
  `bin/release/simple` binary is refreshed to match current
  source/runtime/compiler behavior.
- Hosted SimpleOS feature specs rerun during the later doc-alignment passes
  still pass, and the profile report contract plus numeric cross-language gate
  pass against
  `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`.
- The 2026-06-14 interpreter-run SimpleOS refresh in
  `doc/09_report/simpleos_multicore_green_evidence_2026-06-07.md` reran the
  cooperative, multicore-green scheduler, green-channel wake, and final
  handoff blocker specs from `/tmp/simple-pherallel-continue-jj` after
  shared-main sync; it keeps hosted SimpleOS support current without changing
  the already closed opt-in live-QEMU final-handoff claim.
- This 2026-06-13 slice used Docker-isolated focused checks with `SIMPLE_BIN`
  pinned to a current-source compiler, passed
  `test/05_perf/profile_scripts/concurrency_api_contract_test.shs` with
  `positive_fixtures=6`, generated misuse contract `misuse_fixtures=11`,
  checked-in fixture contract `checked_in_misuse_fixtures=29`,
  total shell-enforced `total_misuse_fixtures=40`, and
  `public_multicore_green_sliced_result=19 used_runtime_pool=true`, then passed
  `test/03_system/feature/usage/concurrency_api_misuse_spec.spl` with seven
  scenarios and the same shell-enforced misuse inventory.
- The checked-in release-binary stale blocker is now part of the canonical
  feature row and tracking SSpec as a mitigated deploy-artifact boundary, so
  future agents cannot use `bin/release/simple` as authoritative
  multicore-green native evidence unless its platform delegate exists and
  passes `--version`.
- The later 2026-06-13 cross-language profile gate hardening requires
  `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl` and the
  generated manual to assert that every checked-in cooperative-green worker and
  fanout row says `current OS thread`, while still rejecting `pool_used=`,
  `parallelism=`, and `M:N` wording for that API.
- The later 2026-06-13 SimpleOS QEMU guard hardening requires
  `test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl` and the
  generated manual to prove the scheduler-only live lane does not print
  `HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, or
  `USER_SYSCALL_PASS=true`; those final markers remain exclusive to the
  `SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1` lane.

## Current Sync Status (2026-06-14)

- The current jj workspace is rebased on `main@origin` for the multicore-green
  lane.
- Go scheduler research is refreshed against official 2026-06-14 Go docs and
  records Go 1.25 container-aware `GOMAXPROCS` plus `containermaxprocs` as
  domain context. The checked-in profile gates still require
  `GOMAXPROCS=$CPU_WORKERS` so Simple-vs-Go comparisons do not depend on
  volatile host or Docker defaults.
- The 2026-06-14 status-alignment slice updates the report index, agent-task
  plan, system-test plan, tracking SSpec, and generated tracking manual so
  future multicore-green status reads see the latest interpreter-run SimpleOS
  cooperative, multicore scheduler, green-channel wake, and final handoff
  blocker evidence without depending on a volatile pushed commit id.
- Profile contract output keeps `report_index_checked` and
  `agent_task_plan_checked` release-visible so the report index and agent
  handoff cannot silently point future agents at stale evidence.
- Latest interpreter-run SimpleOS cooperative, multicore scheduler,
  green-channel, and final handoff blocker evidence remains the current
  scheduler-only SimpleOS guard.
- Focused verification for that slice passed: profile report contract, SPipe
  dev command wiring, local interpreter tracking SSpec with 13 scenarios, and
  the generated-spec layout guard returning `0`.
- The later 2026-06-14 safepoint slice added
  `multicore_green_safepoint()` as an explicit runtime/compiler poll hook and
  executable standalone-native fairness evidence while keeping ordinary
  `multicore_green_spawn` closure preemption future work.
