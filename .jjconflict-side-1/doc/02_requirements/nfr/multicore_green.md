# Multicore Green Non-Functional Requirements

Date: 2026-06-07

Selected NFR path: Evidence Integrity Gate, Performance Parity Budget, API
Stability And Misuse Diagnostics, and SimpleOS Hardware Proof Gate.

## Requirements

- NFR-MCG-001: No report, guide, release note, or SPipe manual may claim
  Go-like M:N CPU parallelism unless the evidence row has `used_runtime_pool()`
  / `pool_used=` evidence plus public runtime-pool counter drain evidence
  (`counter_delta=<submitted>/<completed>,pending=0,busy=0,blocked=0`), or
  SimpleOS scheduler evidence.
- NFR-MCG-002: Cooperative green rows must remain classified as current-carrier,
  non-CPU-parallel work.
- NFR-MCG-003: Cross-language performance reports must include OS-thread,
  cooperative-green, multicore-green, C pthread, Go goroutine, large-fanout,
  Simple-vs-Go-vs-C stress, hosted `parallelism=requested/actual`,
  public `counter_delta=submitted/completed,pending=0,busy=0,blocked=0`
  evidence for hosted multicore-green rows,
  Go runtime/scheduler metadata, Go `GOMAXPROCS` pinned to `CPU_WORKERS` unless
  explicitly overridden, artifact-size, and RSS evidence. The report contract
  must also preserve Docker Simple binary auto-selection wording that probes
  candidates with `--version` and skips stale release wrappers.
- NFR-MCG-004: Simple native OS-thread and multicore-green rows must stay within
  the documented ratios in `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl`
  for the checked-in Docker contract profile.
- NFR-MCG-005: The ordinary large-fanout section and the large-fanout stress
  section must prove Go goroutine fanout beats one-pthread-per-task C fanout so
  the benchmark distinguishes M:N scheduling from OS-thread creation.
- NFR-MCG-006: Any miss against the performance budget must create or update a
  measured blocker under `doc/08_tracking/bug/`.
- NFR-MCG-007: Public APIs keep meaningful names: `thread_spawn`,
  `thread_spawn_with_args`, `green_spawn`, `cooperative_green_spawn`,
  `cooperative_green_spawn_value`, `multicore_green_spawn`,
  `multicore_green_spawn_sliced`, and `task_spawn`.
- NFR-MCG-008: Numbered aliases remain rejected by `simple check` with
  actionable replacement diagnostics.
- NFR-MCG-009: User code should not need C or Rust rewrites to benefit from
  optimizer, runtime-pool, or scheduler improvements.
- NFR-MCG-010: Hosted SimpleOS specs must prove logical green scheduling,
  channel wake, remote enqueue/IPI state, per-CPU dispatch, and topology growth.
- NFR-MCG-011: Live QEMU evidence is required before claiming SimpleOS hardware
  or AP behavior.
- NFR-MCG-012: Final hardware context-switch handoff claims must remain backed
  by live QEMU evidence containing `HW_HANDOFF_PASS=true`,
  `USER_ENTRY_PASS=true`, and `USER_SYSCALL_PASS=true` from the real AP
  ring/user path.

## Verification Gates

- `sh test/05_perf/profile_scripts/profile_report_contract_test.shs`
- `sh test/05_perf/profile_scripts/profile_report_contract_negative_test.shs`
  including the `docker_simple_binary_probe_wording_corrupt` failure case
- `sh test/05_perf/profile_scripts/profile_help_contract_test.shs`
- `sh test/05_perf/profile_scripts/profile_binary_autoselect_test.shs`
- `sh test/05_perf/profile_scripts/profile_docker_isolation_contract_test.shs`
- `sh test/05_perf/profile_scripts/concurrency_api_contract_test.shs`
- `src/compiler_rust/target/debug/simple test test/05_perf/stress/multicore_green_cross_language_gate_spec.spl --mode=interpreter --clean`
- `src/compiler_rust/target/debug/simple test test/05_perf/stress/multicore_green_large_profile_gate_spec.spl --mode=interpreter --clean`
- `src/compiler_rust/target/debug/simple test test/05_perf/stress/multicore_green_fanout_spec.spl --mode=interpreter --clean`
- `src/compiler_rust/target/debug/simple test test/03_system/feature/usage/concurrency_api_misuse_spec.spl --mode=interpreter --clean`
- `src/compiler_rust/target/debug/simple test test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl --mode=interpreter`
- `src/compiler_rust/target/debug/simple test test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl --mode=interpreter`
- `src/compiler_rust/target/debug/simple test test/03_system/os/simpleos/feature/simpleos_green_channel_wake_spec.spl --mode=interpreter`
- `src/compiler_rust/target/debug/simple test test/01_unit/os/kernel/scheduler/scheduler_green_user_handoff_spec.spl --mode=interpreter --clean`
- `src/compiler_rust/target/debug/simple test test/03_system/os/simpleos/feature/simpleos_green_hardware_handoff_blocker_spec.spl --mode=interpreter`
- `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1 src/compiler_rust/target/debug/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean` when live QEMU hardware/AP evidence is claimed.
- `SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1 src/compiler_rust/target/debug/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean` when final AP ring/user handoff evidence is claimed; the serial proof must include `HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, and `USER_SYSCALL_PASS=true`.
