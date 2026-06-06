# Multicore Green Feature Requirement Options

Date: 2026-06-06

Scope: Simple host and SimpleOS support for Go-like CPU-parallel green work,
while keeping `thread_spawn`, `cooperative_green_spawn`, and
`multicore_green_spawn` semantically distinct.

These are options only. Final feature requirements require user selection.
Unchosen options should be deleted, not archived.

## Evidence-Only Stabilization

Targets:
- Keep the current public API split: `thread_spawn` for OS threads,
  `cooperative_green_spawn` for current-carrier cooperative work, and
  `multicore_green_spawn` for bounded runtime-pool value work.
- Keep profile scripts and reports honest about which rows are OS thread,
  cooperative green, runtime-pool M:N candidate, C pthread, and Go goroutine.
- Track remaining native explicit-argument, SMF cooperative-green, SMF
  multicore-green, and SimpleOS hardware handoff blockers.

Pros:
- Lowest risk.
- Preserves all existing user-facing APIs.
- Matches the evidence already present in SPipe specs and reports.

Cons:
- Does not complete a final scheduler-aware M:N green runtime.
- Leaves SimpleOS support as carrier-dispatch proof rather than full context
  handoff.

Effort: Small.

Acceptance evidence:
- Cross-language profile contract passes.
- `multicore_green_cross_language_gate_spec.spl` passes.
- `multicore_green_fanout_spec.spl` passes.
- SimpleOS green-carrier QEMU proof remains documented as partial hardware
  evidence.

## Host Runtime-Pool M:N

Targets:
- Treat `multicore_green_spawn` as the host-side M:N API only when every handle
  proves `used_runtime_pool()`.
- Add or keep native entry-closure evidence that runtime-pool work is CPU
  parallel and does not silently fall back inline.
- Keep `cooperative_green_spawn` documented and tested as non-M:N current-carrier
  work.
- Keep `thread_spawn` as the explicit one-OS-thread-per-spawn baseline.

Pros:
- Directly advances Go-like CPU parallelism on hosted Simple.
- Keeps Pure Simple code as the user-facing layer over the runtime pool.
- Gives profile scripts a concrete M:N row that is separate from C pthreads.

Cons:
- Does not by itself implement SimpleOS hardware context-switch handoff.
- Still relies on runtime-pool ABI availability in native builds.
- Requires continued blocker tracking for SMF and explicit-argument thread
  paths.

Effort: Medium.

Acceptance evidence:
- Native multicore-green workload fails if runtime-pool evidence is missing.
- Cross-language report includes numeric Simple multicore-green native rows and
  `used_runtime_pool()` evidence.
- Guide docs never describe cooperative green as Go M:N.

## Scheduler-Aware SimpleOS Green Runtime

Targets:
- Extend SimpleOS green-carrier proof from scheduler-visible dispatch to real
  scheduler-owned green runtime behavior across APs.
- Integrate green task state, channel wake, park/unpark, and per-CPU carrier
  queues with SimpleOS scheduling.
- Add live QEMU evidence for AP green dispatch and a separate future gate for
  hardware context-switch handoff.

Pros:
- Moves SimpleOS toward first-class green-thread support.
- Uses existing SimpleOS SMP, IPI, and scheduler-owned green execution state.
- Gives kernel-side evidence instead of host-only runtime-pool evidence.

Cons:
- Larger kernel/runtime surface.
- Harder to verify without opt-in QEMU runs.
- Full syscall/blocking and context-switch integration is higher risk than host
  runtime-pool work.

Effort: Large.

Acceptance evidence:
- Hosted SimpleOS SPipe specs pass for cooperative green, multicore green, and
  green-channel wake.
- Live QEMU green-carrier proof passes with AP startup and CPU1 dispatch.
- Remaining context-switch handoff gaps are explicitly tracked until proven.

## Full Go-Like Runtime Roadmap

Targets:
- Deliver host runtime-pool M:N, SimpleOS carrier scheduling, blocking
  integration, work stealing or per-worker queues, and a parallelism-limit
  control similar in role to Go's `GOMAXPROCS`.
- Add preemption or compiler-inserted yield points before claiming tight-loop
  fairness comparable to modern Go.
- Keep C, Go, and Rust as evidence baselines or implementation contexts, not as
  replacements for Simple user-facing APIs.

Pros:
- Best match for the final Go-like objective.
- Makes fairness, blocking, and CPU utilization explicit instead of relying on
  benchmark-only evidence.
- Gives a coherent end-to-end path across hosted Simple and SimpleOS.

Cons:
- Largest scope and longest verification path.
- Requires staged architecture, design, and several release-blocking tests.
- Needs careful compatibility handling for existing concurrency APIs.

Effort: Extra Large.

Acceptance evidence:
- Requirements, architecture, design, SPipe specs, generated manuals, profile
  evidence, SimpleOS QEMU evidence, and blocker database are all current.
- Native host and SimpleOS lanes prove their claims separately.
- Completion audit shows no M:N claim without corresponding runtime-pool or
  scheduler evidence.

## Selection Needed

Select the feature scope by name before final feature requirements are written.
The likely pragmatic path is either Host Runtime-Pool M:N or Full Go-Like
Runtime Roadmap, depending on whether this cycle should finish host M:N first or
own the full SimpleOS/runtime roadmap now.
