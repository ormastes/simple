# Multicore Green Detail Design

Date: 2026-06-06
Status: selected design for `doc/02_requirements/feature/multicore_green.md`
and `doc/02_requirements/nfr/multicore_green.md`.

## Design Goals

- Keep the Simple API split stable and meaningful.
- Make hosted M:N evidence depend on `MulticoreGreenHandle.used_runtime_pool()`.
- Keep cooperative green deterministic and current-carrier.
- Keep SimpleOS green work scheduler-owned and separate from normal OS tasks.
- Keep profile scripts reproducible and explicit about model differences.

## Public API Design

### OS Thread Baseline

`thread_spawn` creates explicit OS-thread work and returns `ThreadHandle`.
Profile workloads use fork-join `thread_spawn` while
`thread_spawn_with_args` native explicit-argument ABI stays in focused smoke
coverage through `scripts/check/check-thread-spawn-with-args-native.shs`.

Design rule: OS-thread rows must not be compared as green-thread rows. They are
the platform-thread baseline, equivalent in model to C pthread fanout.

### Cooperative Green Queue

`cooperative_green_spawn` and `cooperative_green_spawn_value` wrap the
single-carrier `green_thread` queue.

Data structures:

- `GREEN_VALUE_READY_COUNT` and `GREEN_VALUE_DONE_COUNT` for queued eager
  results.
- `GreenThreadHandle.value_order` and `GreenThreadHandle.value_result` for
  completion checks and joins without storing delayed function values.

Behavior:

- `cooperative_green_spawn(task)` evaluates the function when scheduled, then
  queues the result through the same value path as
  `cooperative_green_spawn_value(result)`.
- `cooperative_green_run_one` advances one ready value on the current OS
  thread.
- `cooperative_green_run_all` drains currently ready work.
- Join returns a completed result or zero for not-yet-done work.

Design rule: this path is lightweight and deterministic but not CPU parallel,
preemptive, or Go M:N.

### Multicore Green Runtime-Pool Candidate

`multicore_green_spawn(task)` calls `rt_pool_submit(task)`.

Data structure:

- `MulticoreGreenHandle.native_handle`
- `MulticoreGreenHandle.inline_done`
- `MulticoreGreenHandle.inline_result`

Behavior:

- Positive `native_handle` means runtime-pool acceptance.
- Zero `native_handle` runs the task inline and records fallback result.
- `used_runtime_pool()` is true only for positive handles.
- `ran_inline_fallback()` is true only for fallback.
- `join()` delegates to `rt_pool_join` for native handles and otherwise returns
  the inline result.
- `multicore_green_uses_work_stealing()` is true only when the hosted native
  pool reports per-worker queues with stealing rather than a single global FIFO.

Design rule: only positive-handle work with work-stealing evidence can support
hosted M:N claims. Inline fallback is correct behavior but not M:N evidence.

## SimpleOS Design

### Logical Green Task State

`green_task.spl` owns green task lifecycle state: runnable, parked, unparked,
done, and carrier CPU preservation.

Design rule: logical green tasks are not normal OS tasks. They may produce a
typed scheduler intent, but they must not overwrite normal current-task state.

### Carrier Queue And Wake Intent

`green_carrier.spl` owns enqueue and dispatch decisions.

Key structures:

- `GreenCarrierEnqueueDecision`
- `GreenCarrierRunQueueState`
- `GreenCarrierApplyResult`
- `GreenCarrierDispatchResult`
- `GreenCarrierSchedulerIntent`
- `GreenCarrierExecutionState`
- `GreenCarrierExecutionResult`

Behavior:

- Runnable tasks enqueue to a bounded carrier queue.
- Parked or done tasks do not enqueue.
- Remote target CPU enqueue records a reschedule IPI intent.
- Dispatch selects queued green work for a carrier CPU.
- Scheduler intent applies to the green execution lane.

### Freestanding QEMU Probe Path

`green_carrier_fixed_spawn_cpu` and `green_carrier_fixed_run_task` avoid heap
and text-heavy state for small SimpleOS x86_64 QEMU probes.

Design rule: fixed-slot helpers are proof adapters, not replacements for the
hosted scheduler-facing API.

## Profile Script Design

`scripts/check/check-cross-language-perf.shs` generates these model-separated
rows:

- Simple OS thread via `thread_spawn`
- Simple cooperative green via `cooperative_green_spawn_value`
- Simple multicore green via `multicore_green_spawn`
- C pthreads
- Go goroutines
- Go-vs-C isolated large-fanout stress
- RSS and artifact-size evidence

The profile contract test rejects missing model text and missing evidence rows.
SPipe perf specs parse the checked-in report to keep numeric evidence from
drifting silently.

## Error Handling And Misuse

- Numbered concurrency aliases are rejected by `simple check` with actionable
  replacement names.
- `thread_spawn_with_args` stays documented as focused native ABI coverage, not
  as the profile OS-thread baseline. Profile rows continue to use `thread_spawn`
  so scheduler and fanout comparisons stay model-pure.
- Profile reports classify SMF failures as blockers, not as scheduling
  timings.
- Docs must not call cooperative green M:N.

## Verification Design

Host API coverage:

- `test/01_unit/lib/nogc_async_mut/cooperative_green_spec.spl`
- `test/01_unit/lib/nogc_async_mut/multicore_green_spec.spl`
- `test/01_unit/lib/nogc_async_mut/multicore_green_native.spl`

SimpleOS coverage:

- `test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl`
- `test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl`
  covers scheduler-owned carrier state plus named runtime, timer-interrupt,
  and compiler safepoint adapters.
- `test/03_system/os/simpleos/feature/simpleos_green_channel_wake_spec.spl`
- `test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl`

Profile coverage:

- `test/05_perf/profile_scripts/profile_report_contract_test.shs`
- `test/05_perf/stress/multicore_green_fanout_spec.spl`
- `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl`

Repository guards:

- `git diff --check`
- `find doc/06_spec -name '*_spec.spl' | wc -l`
- `sh scripts/setup/install-spipe-dev-command.shs --check`

## Open Design Decisions

- Scheduler-owned parallelism handoff: the hosted runtime-pool facade now has
  `multicore_green_set_parallelism`, `multicore_green_parallelism`, and
  work-stealing evidence, but the final SimpleOS scheduler-aware green runtime
  still needs the handoff from hosted pool limits to scheduler-owned carrier
  limits, with the final AP ring/user context-switch proof tracked in
  `doc/08_tracking/bug/simpleos_green_hardware_context_switch_handoff_2026-06-07.md`.
- Preemption strategy: compiler-inserted yields, runtime safepoints, or an
  explicit cooperative-only guarantee until later.
