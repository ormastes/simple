# Multicore Green Non-Functional Requirements

Date: 2026-06-07

Selected NFR path: Evidence Integrity Gate, Performance Parity Budget, API
Stability And Misuse Diagnostics, and SimpleOS Hardware Proof Gate.

## Requirements

- NFR-MCG-001: No report, guide, release note, or SPipe manual may claim
  Go-like M:N CPU parallelism unless the evidence row has `used_runtime_pool()`
  / `pool_used=` evidence or SimpleOS scheduler evidence.
- NFR-MCG-002: Cooperative green rows must remain classified as current-carrier,
  non-CPU-parallel work.
- NFR-MCG-003: Cross-language performance reports must include OS-thread,
  cooperative-green, multicore-green, C pthread, Go goroutine, large-fanout,
  Simple-vs-Go-vs-C stress, hosted `parallelism=requested/actual`,
  Go runtime/scheduler metadata, artifact-size, and RSS evidence.
- NFR-MCG-004: Simple native OS-thread and multicore-green rows must stay within
  the documented ratios in `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl`
  for the checked-in smoke profile.
- NFR-MCG-005: The large-fanout stress section must prove Go goroutine fanout
  beats one-pthread-per-task C fanout so the benchmark distinguishes M:N
  scheduling from OS-thread creation.
- NFR-MCG-006: Any miss against the performance budget must create or update a
  measured blocker under `doc/08_tracking/bug/`.
- NFR-MCG-007: Public APIs keep meaningful names: `thread_spawn`,
  `thread_spawn_with_args`, `green_spawn`, `cooperative_green_spawn`,
  `cooperative_green_spawn_value`, `multicore_green_spawn`, and `task_spawn`.
- NFR-MCG-008: Numbered aliases remain rejected by `simple check` with
  actionable replacement diagnostics.
- NFR-MCG-009: User code should not need C or Rust rewrites to benefit from
  optimizer, runtime-pool, or scheduler improvements.
- NFR-MCG-010: Hosted SimpleOS specs must prove logical green scheduling,
  channel wake, remote enqueue/IPI state, per-CPU dispatch, and topology growth.
- NFR-MCG-011: Live QEMU evidence is required before claiming SimpleOS hardware
  or AP behavior.
- NFR-MCG-012: Final hardware context-switch handoff remains tracked in
  `doc/08_tracking/bug/simpleos_green_hardware_context_switch_handoff_2026-06-07.md`
  until a live guest proves `HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, and
  `USER_SYSCALL_PASS=true` from the real AP ring/user path.

## Verification Gates

- `sh test/05_perf/profile_scripts/profile_report_contract_test.shs cross_language scripts/check/check-cross-language-perf.shs doc/09_report/cross_language_perf_parallel_smoke.md`
- `sh test/05_perf/profile_scripts/profile_report_contract_test.shs cross_language scripts/check/check-cross-language-perf.shs doc/09_report/cross_language_perf_parallel_large_2026-06-07.md`
- `bin/simple test test/05_perf/stress/multicore_green_cross_language_gate_spec.spl --mode=interpreter`
- `bin/simple test test/05_perf/stress/multicore_green_large_profile_gate_spec.spl --mode=interpreter`
- `bin/simple test test/05_perf/stress/multicore_green_fanout_spec.spl --mode=interpreter`
- `bin/simple test test/03_system/feature/usage/concurrency_api_misuse_spec.spl --mode=interpreter`
- `bin/simple test test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl --mode=interpreter`
- `bin/simple test test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl --mode=interpreter`
- `bin/simple test test/03_system/os/simpleos/feature/simpleos_green_channel_wake_spec.spl --mode=interpreter`
- `bin/simple test test/01_unit/os/kernel/scheduler/scheduler_green_user_handoff_spec.spl --mode=interpreter`
- `bin/simple test test/03_system/os/simpleos/feature/simpleos_green_hardware_handoff_blocker_spec.spl --mode=interpreter`
- `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1 bin/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean` when live QEMU hardware/AP evidence is claimed.
- `SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1 bin/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean` when final AP ring/user handoff evidence is claimed; the serial proof must include `HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, and `USER_SYSCALL_PASS=true`.
