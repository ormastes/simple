# Feature: multicore-green

## Raw Request

$sp_dev research about go thread. and others plan spawn agent plan and update doc and the profile scripts.  it should support m:n cpu pherallel like go. cooperative_green multicore_green should be supported. it also supported on simple os. if needed update simple os with sspec tests. however often sync with gh

## Task Type

feature

## Refined Goal

Deliver and verify a Simple concurrency lane that clearly separates OS threads, cooperative green threads, and pool-backed multicore green work while providing Go/C comparison evidence, SimpleOS evidence, current documentation, and profile-script gates.

## Acceptance Criteria

- AC-1: Go goroutine, C pthread, Simple `thread_spawn`, `cooperative_green_spawn`, `multicore_green_spawn`, and `task_spawn` semantics are researched and documented with no misleading M:N claims.
- AC-2: Public docs and coding guidance distinguish `thread_spawn` as OS-thread work, cooperative green APIs as current-carrier queue work, and `multicore_green_spawn` as pool-backed M:N candidate work only with runtime-pool evidence.
- AC-3: Profile scripts use existing canonical profile harnesses, include OS-thread, cooperative-green, multicore-green, Go, and C rows, and reject numbered API aliases such as `thread_spawn2`.
- AC-4: Perf reports prove Go-vs-C fanout behavior and Simple multicore-green native rows with `used_runtime_pool()` / `pool_used=` evidence.
- AC-5: Pure Simple implementation, generated workloads, and executable perf specs avoid unrolled numbered handles where compact semantic loops and handle arrays preserve behavior.
- AC-6: SimpleOS cooperative-green and multicore-green support has executable SPipe specs, generated manuals, and current evidence reports.
- AC-7: Misuse and API-shape checks reject wrong-surface imports, numbered API aliases, bad public argument shapes, and fallback rows that pretend to be runtime-pool M:N work.
- AC-8: Final feature and NFR requirement documents are written from user-selected options; unselected options are removed per repository process.
- AC-9: Verification includes SPipe command wiring, generated-spec layout guard, relevant unit/system/perf specs, profile contract, and GitHub sync.

## Scope Exclusions

- Do not replace Simple user-facing concurrency APIs with C/Rust APIs.
- Do not claim cooperative green APIs are Go-style M:N CPU parallelism.

## Phase

go-runtime-hardening

## Log

- dev: Created state file with acceptance criteria for the multicore green SPipe lane.
- audit: Current implementation/profile/docs evidence is present for AC-1 through
  AC-9 after selected requirements were written.
- requirements: User selected `Full Go-Like Runtime Roadmap`; final feature and
  NFR requirements were written and option docs were removed.
- implementation: Added hosted multicore-green parallelism control through
  `multicore_green_set_parallelism` / `multicore_green_parallelism` and
  `rt_pool_set_parallelism` / `rt_pool_get_parallelism`; profile rows now
  require `parallelism=requested/actual` evidence in addition to `pool_used`.
- implementation: Reworked cross-language profile workload generation and
  multicore-green fanout SSpec to use semantic typed handle arrays instead of
  numbered `h0` / `h1` style handles; the profile report contract now rejects
  numbered generated handles.
- evidence: Regenerated `doc/09_report/cross_language_perf_parallel_smoke.md`
  with capture-free generated Simple workers. Native regular parallel, fanout,
  and stress multicore-green rows now pass with `pool_used=N/N` and
  `parallelism=requested/actual` evidence.
- evidence: Added dated large profile evidence in
  `doc/09_report/cross_language_perf_parallel_large_2026-06-07.md` with
  100 CPU workers, 1000 fanout workers, and 2000 stress workers. The large
  profile shows Go goroutine fanout beating C pthread fanout and Simple
  multicore-green native fanout/stress beating C with full runtime-pool
  evidence. `test/05_perf/stress/multicore_green_large_profile_gate_spec.spl`
  gates this report.
- verification: Re-ran SimpleOS cooperative green, multicore green scheduler,
  green-channel wake, default QEMU gate, and live QEMU green-carrier proof with
  the rebuilt compiler; live QEMU passed in 40469ms.
- implementation: Added SimpleOS scheduler-owned green carrier parallelism
  state and helper APIs. The active carrier count is topology-bounded while the
  requested limit is preserved, advancing the selected full Go-like roadmap
  without changing user-facing concurrency APIs. Hardware handoff, blocking
  integration, work stealing, and preemption remain explicit follow-up gates.
- verification: `green_carrier.spl` check passed and
  `test/01_unit/os/kernel/scheduler/green_carrier_spec.spl` passed 30
  examples, including carrier-limit clamp, invalid-topology, and
  topology-growth coverage.
- implementation: Wired the SimpleOS carrier parallelism state into the real
  `Scheduler`, with scheduler-facing set/get methods and topology-change
  recomputation that preserves the requested carrier count.
- verification: `scheduler.spl` check passed and
  `test/01_unit/os/kernel/scheduler/scheduler_green_parallelism_spec.spl`
  passed 4 examples. A broad `scheduler_spec.spl` run timed out at 120s, so the
  focused spec is the direct evidence for this scheduler-owned parallelism
  increment.
- implementation: Enforced the active SimpleOS green carrier limit in
  `Scheduler.apply_green_scheduler_intent`. Runnable intents targeting inactive
  carrier CPUs are rejected and counted instead of recording execution.
- verification: `green_carrier_spec.spl` passed 32 examples,
  `scheduler_green_parallelism_spec.spl` passed 7 examples, and
  `simpleos_multicore_green_spec.spl` passed 3 examples after default carrier
  limits were changed to follow topology growth/shrink while explicit requests
  remain preserved. The focused scheduler spec also proves dispatch can run on
  carriers activated by topology growth and rejects inactive-carrier dispatch.
- implementation: Added `green_carrier_dispatch_next_with_limit` so inactive
  carrier backpressure is applied before queue removal. Inactive-carrier
  dispatch now preserves queued work instead of relying on scheduler rejection
  after dequeue.
- verification: `green_carrier_spec.spl` passed 33 examples,
  `scheduler_green_parallelism_spec.spl` passed 7 examples, and
  `simpleos_multicore_green_spec.spl` passed 3 examples after the non-dropping
  dispatch helper was added.
- implementation: Added carrier-queue rebalance helpers so green-worker
  rebalance decisions can move queued work from inactive or overloaded carriers
  onto active carriers before dispatch.
- verification: `green_carrier_spec.spl` passed 36 examples,
  `scheduler_green_parallelism_spec.spl` passed 8 examples, and
  `simpleos_multicore_green_spec.spl` passed 3 examples after rebalance helpers
  were added.
- implementation: Added `Scheduler.rebalance_green_carrier_queues`, a
  scheduler-owned wrapper that applies green-worker rebalance decisions using
  the scheduler's current active carrier limit.
- verification: `scheduler.spl` check passed,
  `scheduler_green_parallelism_spec.spl` passed 8 examples, and
  `simpleos_multicore_green_spec.spl` passed 3 examples after the scheduler
  rebalance wrapper replaced the direct free-helper call in scheduler evidence.
- implementation: Added `Scheduler.rebalance_green_carrier_queues_from_depth`
  so the scheduler can derive green-worker rebalance decisions from live
  carrier queue depths before applying its active carrier limit.
- verification: `scheduler.spl` check passed,
  `scheduler_green_parallelism_spec.spl` passed 9 examples, and
  `simpleos_multicore_green_spec.spl` passed 3 examples for the queue-depth
  rebalance wrapper.
- implementation: Added `Scheduler.rebalance_green_carrier_queues_until_stable`
  with an explicit move budget, plus `GreenCarrierRebalancePassResult`, so the
  scheduler can repeatedly drain inactive carrier queues without unbounded
  loops.
- verification: `scheduler_green_parallelism_spec.spl` passed 11 examples,
  `green_carrier_spec.spl` passed 36 examples, and
  `simpleos_multicore_green_spec.spl` passed 3 examples after the bounded
  repeated rebalance pass was added.
- implementation: Added `Scheduler.run_green_carrier_once`, a scheduler-owned
  one-step carrier runner that dispatches through the active carrier limit and
  applies the resulting green scheduler intent while preserving inactive-carrier
  queued work.
- verification: `scheduler.spl` and `green_carrier.spl` checks passed,
  `scheduler_green_parallelism_spec.spl` passed 13 examples,
  `green_carrier_spec.spl` passed 36 examples, and
  `simpleos_multicore_green_spec.spl` passed 3 examples after the run-step
  helper.
- implementation: Added `Scheduler.run_green_carrier_active_pass`, a bounded
  active-worker pass that performs budgeted inactive-carrier rebalance and then
  attempts one run step per active carrier.
- verification: `scheduler.spl` and `green_carrier.spl` checks passed, and
  `scheduler_green_parallelism_spec.spl` passed 15 examples for active-worker
  pass and rebalance-before-run behavior.
- implementation: Added `Scheduler.run_green_channel_wake_pass`, which converts
  green-channel send/unpark output into a carrier enqueue and runs the bounded
  active-carrier pass only after a successful wake enqueue.
- verification: `simpleos_green_channel_wake_spec.spl` passed 4 examples,
  proving channel wake can re-enter scheduler-owned active carrier execution;
  `scheduler_green_parallelism_spec.spl` still passed 15 examples,
  `green_carrier_spec.spl` passed 36 examples, and
  `simpleos_multicore_green_spec.spl` passed 3 examples.
- implementation: Added `Scheduler.run_green_carrier_until_blocked_or_budget`,
  a bounded scheduler-owned worker-loop primitive that repeats active-carrier
  passes until no active work remains or the explicit pass budget is exhausted.
- verification: `scheduler.spl` and `green_carrier.spl` checks passed, and
  `scheduler_green_parallelism_spec.spl` passed 17 examples for drain-to-idle
  and run-budget-exhausted loop behavior.
- implementation: Added `Scheduler.yield_green_current_on_cpu`, a cooperative
  green fairness hook that requeues the current green task and clears the
  current slot only after successful requeue.
- verification: `scheduler.spl` and `green_carrier.spl` checks passed, and
  `scheduler_green_parallelism_spec.spl` passed 19 examples for green yield
  requeue and no-current guard behavior.
- implementation: Added `Scheduler.green_timer_tick_on_cpu` plus per-carrier
  green tick budget state, so scheduler ticks can yield/requeue the current
  green task through the existing fairness hook when its time slice expires.
- verification: `scheduler.spl` and `green_carrier.spl` checks passed, and
  `scheduler_green_parallelism_spec.spl` passed 21 examples for tick-budget
  decrement, time-slice yield, and no-current tick behavior.
- implementation: Added `Scheduler.green_timer_tick_active_carriers`, a
  scheduler-owned timer sweep that ticks active carriers only and requeues
  expired green workers through the existing yield path.
- verification: `scheduler.spl` and `green_carrier.spl` checks passed, and
  `scheduler_green_parallelism_spec.spl` passed 23 examples for active-carrier
  timer sweeps and inactive-carrier preservation.
- implementation: Added `Scheduler.green_preemption_safepoint_active_carriers`,
  a scheduler-owned preemption bridge for `timer_interrupt`,
  `runtime_safepoint`, and `compiler_safepoint` sources. Unknown sources return
  `invalid_preemption_source` without ticking or mutating carrier state.
- verification: `scheduler.spl` and `green_carrier.spl` checks passed, and
  `scheduler_green_parallelism_spec.spl` passed 26 examples for timer-interrupt
  preemption, compiler-safepoint entry, and invalid-source misuse coverage.
- implementation: Extended the hosted SimpleOS multicore-green feature spec so
  runtime and timer safepoint sources route through
  `Scheduler.green_preemption_safepoint_active_carriers`, while bad SimpleOS
  source labels are rejected without ticking carriers.
- verification: `simpleos_multicore_green_spec.spl` passed 5 examples for
  SimpleOS remote enqueue, scheduler execution state, topology growth,
  preemption safepoints, and invalid-source misuse coverage.
- profile evidence: `profile_report_contract_test.shs cross_language` passes
  against `doc/09_report/cross_language_perf_parallel_smoke.md`. The dated
  `cross_language_perf_2026-06-06.md` report is historical and does not carry
  the current profile-contract headings.
- implementation: Added `green_carrier_fixed_preempt_running_task` and wired
  the x86_64 green-carrier QEMU probe to emit
  `[green-carrier-qemu] PREEMPT_PASS=true` after a fixed timer-preemption yield
  for the CPU1 green task.
- verification target: `green_carrier_qemu_spec.spl` now requires the
  preemption marker in the live QEMU lane. This advances hardware-facing
  SimpleOS evidence but still does not claim final AP ring/context-switch
  handoff.
- implementation: Added `Scheduler.green_timer_interrupt_active_carriers`, a
  hardware timer-vector adapter that routes `VEC_TIMER` to the
  `timer_interrupt` green preemption source and marks EOI as required while
  leaving green queue ownership with the caller.
- verification: `scheduler.spl` and `green_carrier.spl` checks passed, and
  `scheduler_green_parallelism_spec.spl` passed 27 examples including
  timer-vector, EOI-required, and green-yield evidence.
- implementation: Added named runtime/compiler green safepoint adapters:
  `Scheduler.green_runtime_safepoint_active_carriers` and
  `Scheduler.green_compiler_safepoint_active_carriers`. They delegate to the
  shared preemption bridge with stable source names, avoiding ad hoc string
  call sites for future runtime polling and compiler insertion.
- verification: `scheduler.spl` and `green_carrier.spl` checks passed, and
  `scheduler_green_parallelism_spec.spl` passed 29 examples including named
  runtime and compiler safepoint coverage.

## Completion Audit - 2026-06-07

### Proven Or Strong Evidence

- AC-1 / AC-2: `doc/01_research/lib/threading/go_vs_simple_threads.md`,
  `doc/01_research/local/multicore_green.md`,
  `doc/01_research/domain/multicore_green.md`,
  `doc/07_guide/lib/misc/stdlib.md`,
  `doc/07_guide/compiler/check_perf.md`, and
  `.codex/skills/coding/SKILL.md` distinguish OS threads, cooperative green
  work, runtime-pool multicore green work, Go goroutines, C pthreads, and
  `task_spawn`.
- AC-3 / AC-4 / AC-5: `scripts/check/check-cross-language-perf.shs`,
  `doc/09_report/cross_language_perf_parallel_smoke.md`,
  `doc/09_report/cross_language_perf_parallel_large_2026-06-07.md`,
  `test/05_perf/stress/multicore_green_large_profile_gate_spec.spl`, and
  `test/05_perf/profile_scripts/profile_report_contract_test.shs` use the
  canonical profile harness, compact handle-array generated workloads, Go/C
  comparison rows, large fanout evidence, and `pool_used=` evidence while
  rejecting numbered aliases.
- AC-6: `test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl`,
  `test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl`,
  their generated manuals under `doc/06_spec/test/03_system/os/simpleos/feature/`,
  and `doc/09_report/simpleos_multicore_green_evidence_2026-06-07.md` provide
  current SimpleOS evidence.
- AC-7: `test/03_system/feature/usage/multicore_green_tracking_spec.spl`,
  `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl`,
  `test/05_perf/profile_scripts/concurrency_api_contract_test.shs`, and the
  profile report contract reject wrong-surface claims, numbered API names,
  bad source-level concurrency argument shapes including direct `green_spawn`,
  and runtime-pool fallback rows.
- AC-9: Recent guards include `sh scripts/setup/install-spipe-dev-command.shs
  --check`, `find doc/06_spec -name '*_spec.spl' | wc -l` returning `0`,
  `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl`, and the
  cross-language profile report contract. GitHub is synced through this lane.

### Requirement Selection Complete

- AC-8 is satisfied by `doc/02_requirements/feature/multicore_green.md` and
  `doc/02_requirements/nfr/multicore_green.md`.
- The selected feature scope is `Full Go-Like Runtime Roadmap`.
- The selected NFR path is Evidence Integrity Gate, Performance Parity Budget,
  API Stability And Misuse Diagnostics, and SimpleOS Hardware Proof Gate.
