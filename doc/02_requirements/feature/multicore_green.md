# Multicore Green Feature Requirements

Date: 2026-06-07

Selected scope: Full Go-Like Runtime Roadmap.

## Goal

Simple must provide a Go-like CPU-parallel green-work roadmap that keeps
hosted runtime-pool M:N work, cooperative green queues, OS-thread baselines, and
SimpleOS scheduler work distinct and verifiable.

## Requirements

- REQ-MCG-001: `thread_spawn` remains the explicit one-OS-thread-per-spawn API
  and is the Simple baseline for C pthread-style comparisons.
- REQ-MCG-002: `cooperative_green_spawn` and
  `cooperative_green_spawn_value` remain current-carrier cooperative queue APIs;
  docs, tests, and reports must not describe them as Go-style M:N CPU
  parallelism.
- REQ-MCG-003: `multicore_green_spawn` is the hosted Simple M:N candidate only
  when every handle proves runtime-pool ownership with
  `MulticoreGreenHandle.used_runtime_pool()`.
- REQ-MCG-004: Profile scripts must keep Simple OS-thread, Simple cooperative
  green, Simple multicore green, C pthread, Go goroutine, artifact-size, RSS,
  and large-fanout stress rows separate. Reports must record the Go runtime and
  scheduler metadata, including `GOMAXPROCS`, for M:N comparisons.
- REQ-MCG-005: Generated profile workloads must preserve user-facing Simple API
  semantics, use compact loop/handle-array forms where possible, and avoid
  numbered API aliases or generated numbered handle APIs.
- REQ-MCG-006: SimpleOS support must model logical green tasks separately from
  normal OS tasks and route runnable green work through scheduler-owned carrier
  state.
- REQ-MCG-007: SimpleOS AP/hardware claims require live scheduler or QEMU
  evidence; host-only specs may prove logical behavior but not final hardware
  context-switch handoff. The final handoff blocker is tracked in
  `doc/08_tracking/bug/simpleos_green_hardware_context_switch_handoff_2026-06-07.md`.
- REQ-MCG-008: The roadmap must track blocking integration, work stealing or
  per-worker queues, hosted `multicore_green_set_parallelism` /
  `multicore_green_parallelism` evidence as the initial Go `GOMAXPROCS`-like
  control, scheduler-owned carrier limits beyond the hosted pool, and
  preemption or compiler-inserted yield points before claiming tight-loop
  fairness comparable to modern Go.
- REQ-MCG-009: C, Go, and Rust may be used as baselines, research references,
  seed implementations, or runtime/compiler implementation contexts; they must
  not replace Simple user-facing concurrency APIs.
- REQ-MCG-010: Misuse checks must reject wrong-surface imports, numeric-suffix
  aliases, and profile rows that present inline fallback
  work as runtime-pool M:N evidence.

## Acceptance Evidence

- Go/C/Simple research: `doc/01_research/local/multicore_green.md`,
  `doc/01_research/domain/multicore_green.md`, and
  `doc/01_research/lib/threading/go_vs_simple_threads.md`.
- Architecture/design: `doc/04_architecture/runtime/multicore_green.md` and
  `doc/05_design/multicore_green.md`.
- Host specs: `test/01_unit/lib/nogc_async_mut/cooperative_green_spec.spl`,
  `test/01_unit/lib/nogc_async_mut/multicore_green_spec.spl`, and
  `test/01_unit/lib/nogc_async_mut/multicore_green_native.spl`.
- SimpleOS specs: `test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl`,
  `test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl`,
  `test/03_system/os/simpleos/feature/simpleos_green_channel_wake_spec.spl`,
  `test/01_unit/os/kernel/scheduler/scheduler_green_user_handoff_spec.spl`,
  `test/03_system/os/simpleos/feature/simpleos_green_hardware_handoff_blocker_spec.spl`,
  and `test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl`.
- Performance/profile gates: `scripts/check/check-cross-language-perf.shs`,
  `test/05_perf/profile_scripts/profile_report_contract_test.shs`,
  `test/03_system/feature/usage/concurrency_api_misuse_spec.spl`,
  `test/05_perf/stress/multicore_green_fanout_spec.spl`,
  `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl`,
  `test/05_perf/stress/multicore_green_large_profile_gate_spec.spl`,
  `doc/09_report/cross_language_perf_parallel_smoke.md`, and
  `doc/09_report/cross_language_perf_parallel_large_2026-06-07.md`.
- Hosted parallelism control: `src/runtime/runtime_thread.c`,
  `src/runtime/runtime_thread.h`, and
  `src/lib/nogc_async_mut/concurrent/multicore_green.spl`.
