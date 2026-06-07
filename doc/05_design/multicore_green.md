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
Profile workloads use fork-join `thread_spawn` for the OS-thread baseline.
`thread_spawn_with_args` has focused native ABI smoke coverage, so it remains
separate from scheduler profile rows rather than being treated as a green API.

Design rule: OS-thread rows must not be compared as green-thread rows. They are
the platform-thread baseline, equivalent in model to C pthread fanout.

### Cooperative Green Queue

`cooperative_green_spawn` and `cooperative_green_spawn_value` wrap the
single-carrier `green_thread` queue.

Data structures:

- `GREEN_READY`, `GREEN_READY_HEAD`, `GREEN_READY_COUNT` for queued task ids.
- `GREEN_TASK_IDS` and `GREEN_TASK_RESULTS` for scheduled results.
- `GREEN_DONE_IDS`, `GREEN_RESULT_IDS`, and `GREEN_RESULTS` for join state.
- `GREEN_VALUE_READY_COUNT` and `GREEN_VALUE_DONE_COUNT` for direct value
  scheduling used by profile fanout rows.

Behavior:

- `cooperative_green_run_one` advances one ready value or task result on the
  current OS thread.
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
- `multicore_green_uses_global_fifo_queue()` evidence for the current hosted
  runtime-pool queue model.

Behavior:

- Positive `native_handle` means runtime-pool acceptance.
- Zero `native_handle` runs the task inline and records fallback result.
- `used_runtime_pool()` is true only for positive handles.
- `ran_inline_fallback()` is true only for fallback.
- `join()` delegates to `rt_pool_join` for native handles and otherwise returns
  the inline result.
- `multicore_green_uses_global_fifo_queue()` returns true for the current
  shared FIFO runtime pool. This is honest M:N candidate evidence, not a
  claim of Go-style per-worker queues or work stealing.

Design rule: only positive-handle work can support hosted M:N claims. Inline
fallback is correct behavior but not M:N evidence.

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
- `GreenCarrierParallelismState`

Behavior:

- Runnable tasks enqueue to a bounded carrier queue.
- Parked or done tasks do not enqueue.
- Remote target CPU enqueue records a reschedule IPI intent.
- Dispatch selects queued green work for a carrier CPU.
- Scheduler intent applies to the green execution lane.
- `green_carrier_parallelism_new`, `green_carrier_set_parallelism`,
  `green_carrier_parallelism_for_topology`, and
  `green_carrier_parallelism_limit` preserve explicit requested carrier limits
  while bounding the active carrier count to detected SimpleOS topology.
  Default limits follow topology changes.
- `Scheduler.green_parallelism_state` stores the carrier limit beside
  scheduler-owned green execution state. `set_green_carrier_parallelism`
  updates the requested limit, while `set_topology` recomputes the active
  limit from the preserved request.
- `Scheduler.apply_green_scheduler_intent` rejects runnable dispatch intents
  whose target CPU is outside the active green carrier limit and increments
  rejected green intent accounting.
- `green_carrier_dispatch_next_with_limit` checks the active carrier limit
  before removing a queued task, so inactive-carrier backpressure does not drop
  work.
- `green_carrier_rebalance_one` and `green_carrier_apply_rebalance_decision`
  move queued work from inactive or overloaded carriers to active carriers
  without executing the task during rebalance.
- `Scheduler.rebalance_green_carrier_queues` applies a green-worker rebalance
  decision using `Scheduler.green_parallelism_state.active_limit`, so callers
  do not pass a stale carrier limit.
- `Scheduler.rebalance_green_carrier_queues_from_depth` reads per-CPU carrier
  queue depths and derives the green-worker rebalance decision inside the
  scheduler wrapper.
- `Scheduler.rebalance_green_carrier_queues_until_stable` repeats inactive
  carrier drains with a caller-provided move budget and records why the pass
  stopped.
- `Scheduler.run_green_carrier_once` combines limited carrier dispatch with
  scheduler intent application, returning the updated queues plus dispatch and
  execution evidence for one Go-like worker-loop step.
- `Scheduler.run_green_carrier_active_pass` is the bounded pass primitive for
  the SimpleOS worker loop. It consumes a rebalance move budget, attempts one
  dispatch per active carrier, and returns queue, rebalance, run-count, and
  last-run evidence.
- `Scheduler.run_green_carrier_until_blocked_or_budget` repeats active passes
  under an explicit pass budget, stopping on idle/no-active-work or budget
  exhaustion while preserving unrun queued work.
- `Scheduler.yield_green_current_on_cpu` requeues a running green task on the
  active carrier queue and clears the current slot only after requeue succeeds,
  giving future safepoints or timer preemption a concrete fairness transition.
- `Scheduler.green_timer_tick_on_cpu` records per-carrier green tick budgets,
  decrements them on scheduler tick, and invokes the yield transition on time
  slice expiry.
- `Scheduler.green_timer_tick_active_carriers` runs that tick hook over active
  carriers only, so inactive carrier work is not preempted or requeued behind
  the scheduler-owned parallelism limit.
- `Scheduler.green_preemption_safepoint_active_carriers` wraps the active
  carrier tick sweep with an explicit preemption source contract. Accepted
  sources are `timer_interrupt`, `runtime_safepoint`, and
  `compiler_safepoint`; invalid sources return `invalid_preemption_source`
  without ticking or mutating carrier state.
- `Scheduler.green_timer_interrupt_active_carriers` adapts the x86/APIC
  `VEC_TIMER` interrupt vector to the `timer_interrupt` preemption source and
  records that an end-of-interrupt acknowledgement is required after the
  caller handles the tick.
- `Scheduler.green_runtime_safepoint_active_carriers` and
  `Scheduler.green_compiler_safepoint_active_carriers` provide stable named
  call targets for runtime polling and compiler-inserted safepoints. Both
  delegate to the shared active-carrier preemption bridge and return the same
  evidence shape as generic safepoints.
- `Scheduler.run_green_channel_wake_pass` converts green-channel send/unpark
  output into a carrier enqueue, then runs the bounded active pass only when
  the wake actually enqueued a receiver.

### Freestanding QEMU Probe Path

`green_carrier_fixed_spawn_cpu`, `green_carrier_fixed_run_task`, and
`green_carrier_fixed_preempt_running_task` avoid heap-heavy scheduler state for
small SimpleOS x86_64 QEMU probes. The preemption helper gives the live guest a
freestanding timer-slice yield marker without claiming final AP hardware
context-switch handoff.

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
- Wrong-surface imports are rejected by `simple check` with `E-PAR-003`, and
  bad public argument shapes are rejected with `E-PAR-004`: spawn-style APIs
  including direct `green_spawn` require closures, while
  `multicore_green_set_parallelism` requires an integer worker count.
- `thread_spawn_with_args` native ABI smoke stays separate from scheduler
  profile rows.
- Profile reports reject SMF multicore-green failure rows when used as checked
  M:N evidence; diagnostic failure labels remain available for local triage.
- Docs must not call cooperative green M:N.

## Verification Design

Host API coverage:

- `test/01_unit/lib/nogc_async_mut/cooperative_green_spec.spl`
- `test/01_unit/lib/nogc_async_mut/multicore_green_spec.spl`
- `test/01_unit/lib/nogc_async_mut/multicore_green_native.spl`

SimpleOS coverage:

- `test/01_unit/os/kernel/scheduler/green_carrier_spec.spl`
- `test/01_unit/os/kernel/scheduler/scheduler_green_parallelism_spec.spl`
- `test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl`
- `test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl`
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

- Scheduler-owned parallelism handoff: the hosted runtime-pool facade and
  SimpleOS `Scheduler` now both expose topology-bounded parallelism contracts.
  Remaining work is carrying bounded worker-loop/yield/tick and preemption-
  safepoint sweeps into final AP hardware handoff plus broader blocking
  surfaces.
- Runtime-pool queue model: the hosted runtime currently reports a shared
  FIFO queue. Per-worker queues and stealing remain future optimizer/runtime
  work before claiming Go-like scheduling overhead.
- Preemption strategy: scheduler-owned tick-budget yield, preemption safepoint
  bridge, hardware timer-vector adapter, and named runtime/compiler safepoint
  adapters exist; remaining work is inserting compiler-generated polls,
  choosing runtime poll placement, and wiring final IDT/APIC-owned queue state
  to that hook.
