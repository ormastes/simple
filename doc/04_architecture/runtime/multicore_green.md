# Multicore Green Architecture

Date: 2026-06-06
Status: selected architecture for `doc/02_requirements/feature/multicore_green.md`
and `doc/02_requirements/nfr/multicore_green.md`.

## Scope Boundary

This architecture covers the current and planned Simple concurrency split:

- `thread_spawn` is the explicit OS-thread API.
- `cooperative_green_spawn` and `cooperative_green_spawn_value` are
  current-carrier cooperative queue APIs.
- `multicore_green_spawn` is the hosted Pure Simple M:N candidate only when
  its handle proves runtime-pool acceptance with `used_runtime_pool()`.
- SimpleOS green-carrier support is a scheduler-facing lane for logical green
  tasks, channel wake, AP dispatch evidence, and future hardware handoff.

The architecture deliberately avoids numbered API names and does not use C,
Go, or Rust as user-facing replacements for Simple APIs. C and Go remain
profile baselines; Rust/C runtime code remains bootstrap or ABI
implementation context.

## Architectural Invariants

- No M:N claim without evidence: hosted claims require runtime-pool handles,
  and SimpleOS hardware claims require scheduler/QEMU evidence.
- Cooperative green is never presented as Go-style CPU parallelism.
- Public Simple APIs keep meaningful names and stable behavior.
- Profile scripts must keep OS threads, cooperative green, multicore green,
  C pthreads, and Go goroutines in separate rows.
- SimpleOS logical green task state must not collide with normal OS `TaskId`
  scheduling state.

## Layers

### Public Simple API Layer

Primary paths:

- `src/lib/nogc_sync_mut/concurrent/thread.spl`
- `src/lib/nogc_async_mut/concurrent/cooperative_green.spl`
- `src/lib/nogc_async_mut/concurrent/green_thread.spl`
- `src/lib/nogc_async_mut/concurrent/multicore_green.spl`

Responsibilities:

- Provide stable user-facing names.
- Preserve the semantic difference between OS thread, cooperative queue, and
  runtime-pool M:N candidate.
- Expose join and evidence methods without leaking runtime ABI names into user
  code.

### Runtime Pool ABI Layer

Primary surfaces:

- `rt_pool_submit`
- `rt_pool_join`
- `rt_pool_is_done`

Responsibilities:

- Accept closure work into a bounded native worker pool when linked.
- Return a positive handle only when the runtime pool owns the work.
- Allow `MulticoreGreenHandle.used_runtime_pool()` to be the trust boundary for
  profile and M:N evidence.

### Profile And Evidence Layer

Primary paths:

- `scripts/check/check-cross-language-perf.shs`
- `test/05_perf/profile_scripts/profile_report_contract_test.shs`
- `test/05_perf/stress/multicore_green_fanout_spec.spl`
- `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl`
- `doc/09_report/cross_language_perf_parallel_smoke.md`

Responsibilities:

- Generate and gate reproducible evidence for Simple OS thread, cooperative
  green, multicore green, C pthread, and Go goroutine rows.
- Reject missing or misleading native M:N rows.
- Keep Simple-vs-Go-vs-C large fanout stress explicit so one-pthread-per-task C
  is not mistaken for M:N scheduling and Simple multicore-green stress rows must
  carry runtime-pool evidence.

### SimpleOS Scheduler Layer

Primary paths:

- `src/os/kernel/scheduler/green_task.spl`
- `src/os/kernel/scheduler/green_worker.spl`
- `src/os/kernel/scheduler/green_carrier.spl`
- `src/os/kernel/scheduler/scheduler.spl`
- `src/os/kernel/smp/smp.spl`

Responsibilities:

- Model logical green tasks separately from normal kernel tasks.
- Route runnable green work through bounded carrier queues.
- Send remote reschedule IPI intent for AP work.
- Apply scheduler-owned green execution state separately from normal current
  task state.
- Own a topology-bounded green carrier parallelism limit so hosted
  `multicore_green_set_parallelism` has a matching SimpleOS scheduler contract.
- Provide freestanding fixed-slot helpers for small QEMU probes.

## Data Flow

Hosted runtime-pool path:

- User code calls `multicore_green_spawn`.
- The facade calls `rt_pool_submit`.
- Positive native handle means runtime-pool ownership; zero means inline
  fallback.
- Join and done checks go through `rt_pool_join` and `rt_pool_is_done` only for
  positive native handles.
- Profile rows treat only positive-handle work as M:N candidate evidence.

Cooperative path:

- User code calls `cooperative_green_spawn` or
  `cooperative_green_spawn_value`.
- Work/result enters the current-carrier green queue.
- `cooperative_green_run_one` or `cooperative_green_run_all` drains the queue
  on the current OS thread.
- Profile rows classify this as cooperative queue work, not CPU parallelism.

SimpleOS path:

- Logical green task state is created or woken.
- `green_carrier` creates enqueue and remote wake intent.
- SMP records IPI delivery for remote CPUs.
- Carrier dispatch produces `GreenCarrierSchedulerIntent`.
- `Scheduler.apply_green_scheduler_intent` updates the scheduler-owned green
  execution lane without mutating normal OS task state.
- `GreenCarrierParallelismState` records requested carriers, active
  topology-bounded carriers, and clamp reason for the SimpleOS scheduler lane.
- `Scheduler` owns that carrier parallelism state and recomputes the active
  limit when scheduler topology changes. Explicit requests are preserved;
  default limits follow topology growth or shrink.
- `Scheduler.apply_green_scheduler_intent` rejects runnable intents for CPUs
  outside the active green carrier limit, so inactive carriers cannot record
  scheduler-visible execution.
- `green_carrier_dispatch_next_with_limit` applies the active carrier limit
  before queue removal, preserving queued work as scheduler backpressure for
  inactive carriers.
- `green_carrier_apply_rebalance_decision` turns green-worker rebalance
  decisions into concrete carrier-queue movement, so preserved work can move
  from inactive or overloaded carriers onto active carriers before dispatch.
- QEMU proof currently covers AP startup plus CPU1 fixed-slot dispatch; full
  hardware context-switch handoff remains future work.

## Requirement Mapping

The selected Full Go-Like Runtime Roadmap uses all layers:

- Public Simple API Layer preserves meaningful user APIs and model separation.
- Runtime Pool ABI Layer proves hosted M:N ownership through positive handles,
  `used_runtime_pool()`, and `multicore_green_parallelism()` evidence after
  `multicore_green_set_parallelism(CPU_WORKERS)`.
- Profile And Evidence Layer keeps Go, C pthread, Simple OS-thread,
  cooperative green, and multicore-green rows separate.
- SimpleOS Scheduler Layer owns logical green tasks, carrier queues, remote
  wake/IPI intent, and AP evidence.

Future roadmap work remains explicit: repeated work stealing or per-worker
queue loops, blocking integration, carrying rebalance decisions into final AP
hardware handoff, and preemption or compiler-inserted yield points before
claiming tight-loop fairness comparable to Go.

## Known Gaps

- `thread_spawn_with_args` native explicit-argument ABI remains tracked as a
  blocker, so profile OS-thread rows use `thread_spawn`.
- SMF multicore-green fanout now participates in the same pool-evidence gate as
  native multicore-green. SMF failure classifications remain diagnostic only
  and are rejected by the profile contract when a checked report is used as
  M:N evidence.
- SimpleOS QEMU proof does not yet prove final hardware context-switch handoff.
