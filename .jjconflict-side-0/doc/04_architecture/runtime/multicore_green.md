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
- `rt_pool_uses_global_fifo_queue`
- `rt_pool_uses_work_stealing`
- `rt_pool_submitted_count`
- `rt_pool_completed_count`
- `rt_pool_pending_count`
- `rt_pool_busy_count`
- `rt_pool_blocked_count`
- `rt_pool_safepoint`

Responsibilities:

- Accept closure work into a bounded native worker pool when linked.
- Return a positive handle only when the runtime pool owns the work.
- Allow `MulticoreGreenHandle.used_runtime_pool()` and
  `MulticoreGreenSlicedHandle.used_runtime_pool()` to be the trust boundary for
  profile, hosted sliced-fairness, and M:N evidence.
- Report the hosted queue model in meaningful Simple-facing terms through
  `multicore_green_uses_global_fifo_queue()` and
  `multicore_green_uses_work_stealing()`. Profile evidence treats shared FIFO
  as invalid for M:N claims and requires work-stealing evidence.
- Report submitted/completed task progress and queue/worker state through
  public `multicore_green_*_count()` helpers. These counters are diagnostic
  evidence for runtime-pool progress and starvation checks, not a claim that
  ordinary closures are automatically preempted.
- Expose `rt_pool_safepoint` through the Pure Simple
  `multicore_green_safepoint()` facade as an explicit poll hook. A pool worker
  can mark itself blocked, start compensation capacity, and yield its OS worker
  so queued work can progress. Compiler lowering now inserts this poll at
  Simple loop-body boundaries; broader non-loop/native-call preemption remains a
  separate claim.

### Profile And Evidence Layer

Primary paths:

- `scripts/check/check-cross-language-perf.shs`
- `test/05_perf/profile_scripts/profile_report_contract_test.shs`
- `test/05_perf/profile_scripts/concurrency_api_contract_test.shs`
- `test/05_perf/stress/multicore_green_fanout_spec.spl`
- `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl`
- `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`

Responsibilities:

- Generate and gate reproducible evidence for Simple OS thread, cooperative
  green, multicore green, C pthread, and Go goroutine rows.
- Reject missing or misleading native M:N rows.
- Fail closed when public concurrency APIs drift into numbered aliases, wrong
  import surfaces, direct runtime-pool access, or mutable shared-state captures.
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
- Profile rows print `queue_model=work_stealing` only when the hosted runtime
  pool reports per-worker queues with stealing. The model is still guarded by
  positive runtime-pool handles so reports do not overclaim inline fallback.
- Current hosted fairness boundary is stricter than plain OS-thread yield:
  `rt_pool_worker_main` pops one task and runs `task->entry(task->closure_ptr)`
  to completion before it returns to queue selection, so a tight CPU loop does
  not become requeueable just because it calls `thread_yield()`.
- The current hosted blocking-compensation hook is narrower:
  `src/compiler_rust/runtime/src/executor.rs` only brackets
  `rt_thread_sleep(...)` with `rt_pool_worker_block_begin/end`, so it covers
  real blocking sleep rather than general CPU-loop fairness.
- The explicit hosted safepoint hook is now the runtime/compiler loop step:
  `multicore_green_safepoint()` calls `rt_pool_safepoint` from long hosted
  workers and can grow compensation capacity from `1` to `2` so queued quick
  work runs while the long worker continues. This is executable safepoint
  evidence; raw `thread_yield()` still does not satisfy the same contract.
- `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs` now inserts the
  `rt_pool_safepoint` poll as `HirStmt::While`, `HirStmt::Loop`, and
  `HirStmt::For` lower into native/SMF loop body blocks.

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
- `Scheduler.rebalance_green_carrier_queues` applies those decisions with the
  scheduler-owned active carrier limit, keeping queue movement under the same
  authority as green dispatch.
- `Scheduler.rebalance_green_carrier_queues_from_depth` derives the rebalance
  decision from live carrier queue depths before applying the scheduler-owned
  active carrier limit.
- `Scheduler.rebalance_green_carrier_queues_until_stable` repeats inactive-to-
  active carrier moves with an explicit move budget, so preserved work can be
  drained without unbounded scheduler loops.
- `Scheduler.run_green_carrier_once` is the scheduler-owned one-step carrier
  execution path. It dispatches through the active carrier limit, applies the
  resulting green scheduler intent, and preserves queued work when the target
  carrier is inactive.
- `Scheduler.run_green_carrier_active_pass` is the bounded worker-loop bridge.
  It first performs budgeted inactive-carrier rebalance, then attempts one run
  step per active carrier and reports run counts without claiming unbounded
  preemption.
- `Scheduler.run_green_carrier_until_blocked_or_budget` repeats bounded active
  passes until the carriers report no runnable work or the caller's run budget
  is exhausted. This is the scheduler-owned worker-loop primitive before timer
  preemption is wired in.
- `Scheduler.yield_green_current_on_cpu` is the cooperative fairness hook. It
  requeues the current green task on its active carrier and clears the
  scheduler-owned current slot only after the requeue succeeds.
- `Scheduler.green_timer_tick_on_cpu` is the timer-facing preemption hook. It
  decrements per-carrier green tick budget and calls the cooperative yield path
  when the green time slice expires.
- `Scheduler.green_timer_tick_active_carriers` sweeps that timer hook across
  the active carrier set, preserving inactive carriers until the scheduler
  parallelism limit changes.
- `Scheduler.green_preemption_safepoint_active_carriers` is the shared
  interrupt/runtime/compiler entry contract for green preemption sweeps. It
  accepts meaningful source labels (`timer_interrupt`, `runtime_safepoint`, or
  `compiler_safepoint`), rejects unknown sources without mutating carrier
  state, and delegates accepted sources to the active-carrier timer sweep.
- `Scheduler.green_timer_interrupt_active_carriers` is the hardware timer
  vector adapter for that bridge. It routes `VEC_TIMER` to the
  `timer_interrupt` source, marks that an EOI is required, and returns the
  same active-carrier preemption evidence while leaving queue ownership with
  the caller.
- `Scheduler.green_runtime_safepoint_active_carriers` and
  `Scheduler.green_compiler_safepoint_active_carriers` are the named runtime
  polling and compiler-insertion call targets for the same bridge. They avoid
  stringly call sites while preserving the shared preemption result contract.
- `Scheduler.run_green_channel_wake_pass` composes green-channel unpark output
  with carrier enqueue and the bounded active-carrier pass, so parked channel
  receivers can re-enter scheduler-owned execution without bypassing carrier
  limits.
- QEMU proof currently covers AP startup, CPU1 fixed-slot dispatch, fixed
  timer-preemption yield, scheduler-owned CPU1 green handoff, and the closed
  final AP ring/user marker triplet. The final handoff stays an explicit
  opt-in live gate documented in
  `doc/08_tracking/bug/simpleos_green_hardware_context_switch_handoff_2026-06-07.md`
  so readiness markers and final hardware proof remain separate.

## Requirement Mapping

The selected Full Go-Like Runtime Roadmap uses all layers:

- Public Simple API Layer preserves meaningful user APIs and model separation.
- Runtime Pool ABI Layer proves hosted M:N ownership through positive value and
  sliced handles, `used_runtime_pool()`, `multicore_green_parallelism()`, and `multicore_green_uses_work_stealing()` evidence after
  `multicore_green_set_parallelism(CPU_WORKERS)`.
- Profile And Evidence Layer keeps Go, C pthread, Simple OS-thread,
  cooperative green, and multicore-green rows separate.
- SimpleOS Scheduler Layer owns logical green tasks, carrier queues, remote
  wake/IPI intent, and AP evidence.

Future roadmap work remains explicit: expanding blocking coverage beyond the
current green-channel wake pass and keeping final IDT/APIC-owned queue state
separate from hosted evidence. The supported hosted fairness helper contract for
CPU-heavy Simple work includes the explicit resumable task-slice model exposed by
`multicore_green_spawn_sliced` and compiler-inserted runtime-pool safepoints for
ordinary Simple loop bodies. Profile and API evidence must keep those separate
from broader non-loop/native-call preemption claims. The final AP ring/user
handoff proof itself is now closed by the opt-in live gate.

## Known Gaps

- `thread_spawn_with_args` native explicit-argument ABI has focused smoke
  coverage. Profile OS-thread rows still use `thread_spawn` because they are
  scheduler-baseline rows, not explicit-argument ABI rows.
- Native and SMF multicore-green fanout participate in the pool-evidence gate.
  The historical SMF runtime-pool closure lookup blocker is closed by
  `test/03_system/feature/usage/smf_runtime_pool_closure_regression_spec.spl`;
  current M:N evidence still requires full pool, parallelism, and
  `queue_model=work_stealing` report markers.
- SimpleOS QEMU final hardware context-switch handoff is now proven by the live
  guest marker triplet `HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, and
  `USER_SYSCALL_PASS=true`; keep
  `doc/09_report/simpleos_multicore_green_evidence_2026-06-07.md` current when
  this AP ring/user path changes.
