# SimpleOS Multicore Green Evidence - 2026-06-07

## Scope

This report records the SimpleOS evidence for the multicore-green SPipe lane,
including the opt-in live QEMU green-carrier proof. It does not claim final
ring/user context-switch handoff across APs; the live proof covers AP startup,
fixed-slot CPU1 green dispatch/IPI evidence, fixed timer-preemption yield
evidence, and scheduler-owned CPU1 green handoff through the real `Scheduler`.

## Verified Commands

Commands were refreshed from `/tmp/simple-pherallel-sync` after initializing
the `examples/09_embedded/simple_os` submodule.

```sh
./src/compiler_rust/target/debug/simple test test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl --mode=interpreter --clean
./src/compiler_rust/target/debug/simple test test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl --mode=interpreter --clean
./src/compiler_rust/target/debug/simple test test/03_system/os/simpleos/feature/simpleos_green_channel_wake_spec.spl --mode=interpreter --clean
./src/compiler_rust/target/debug/simple check src/os/kernel/scheduler/green_carrier.spl
./src/compiler_rust/target/debug/simple test test/01_unit/os/kernel/scheduler/green_carrier_spec.spl --mode=interpreter --clean
./src/compiler_rust/target/debug/simple check src/os/kernel/scheduler/scheduler.spl
./src/compiler_rust/target/debug/simple test test/01_unit/os/kernel/scheduler/scheduler_green_parallelism_spec.spl --mode=interpreter --clean
./src/compiler_rust/target/debug/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean
SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1 ./src/compiler_rust/target/debug/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean
```

## Results

| Evidence | Result | Assertions |
|----------|--------|------------|
| SimpleOS cooperative green | PASS | 3 |
| SimpleOS multicore green scheduler contract | PASS | 6 |
| SimpleOS green-channel wake bridge | PASS | 4 |
| SimpleOS green-carrier compile check | PASS | 1 file |
| SimpleOS green-carrier unit contract | PASS | 38 |
| SimpleOS scheduler compile check | PASS | 1 file |
| SimpleOS scheduler green-carrier parallelism | PASS | 29 |
| SimpleOS green-carrier QEMU spec default lane | PASS | 1 |
| SimpleOS green-carrier QEMU live lane | PASS | 1 |

## Current Refresh

After syncing `/tmp/simple-pherallel-sync` to `origin/main` at `45f46b0f6d`,
the non-live SimpleOS green-thread loop was rerun with `--clean` on
2026-06-07. The direct rerun passed:

- cooperative green system contract: 3 assertions
- multicore green scheduler contract: 6 assertions
- green-channel wake bridge: 4 assertions
- green-carrier compile check: 1 file
- green-carrier unit contract: 38 assertions
- scheduler compile check: 1 file
- scheduler green-carrier parallelism: 29 assertions
- QEMU default gate lane: 1 assertion

The live-QEMU row above remains the previously recorded opt-in run. This refresh
does not newly claim final ring/user context-switch handoff across APs.

## Notes

- The default QEMU spec lane proves the opt-in gate is wired and disabled unless
  `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1` is set.
- The live lane passed in 52254ms. The spec built the x86_64 probe, booted a
  two-CPU QEMU guest, and asserted `[smp] AP reached 64-bit entry`,
  `[green-carrier-qemu] PASS=true`, and
  `[green-carrier-qemu] PREEMPT_PASS=true`, and
  `[green-carrier-qemu] SCHED_HANDOFF_PASS=true` in serial output.
- The hosted SimpleOS specs prove scheduler-owned green execution state remains
  separate from normal OS task state. The multicore-green SimpleOS contract now
  also proves named runtime, timer-interrupt, and compiler preemption
  safepoint adapters route through active green carriers, and invalid
  preemption sources are rejected without ticking carriers.
- The green-channel wake bridge now proves a parked receiver can be woken,
  enqueued, budget-rebalanced onto the active carrier set, and run through the
  scheduler-owned active carrier pass.
- The green-carrier unit contract now proves requested-vs-active carrier
  parallelism is scheduler-owned and topology-bounded, with explicit requests
  preserved, default limits aligned to topology changes, and inactive-carrier
  dispatch preserving queued work. It also proves rebalance decisions can move
  queued work from inactive or overloaded carriers onto active carriers.
- The scheduler green-carrier parallelism spec proves the real `Scheduler`
  stores that carrier limit, clamps it to topology, preserves requested
  carriers across topology changes, runs dispatch on carriers activated by
  topology growth, and rejects runnable green dispatch for inactive carriers
  without dropping queued work. It also proves rebalanced inactive-carrier work
  can execute on an active carrier through the scheduler-owned rebalance
  wrapper, including a wrapper path that derives the rebalance decision from
  live carrier queue depths, a bounded repeated pass that drains inactive
  queues or stops when its move budget is exhausted, and a one-step run helper
  that dispatches through the active carrier limit before applying scheduler
  intent. It also proves a bounded active-carrier pass can run one step across
  active workers, rebalance inactive work before running it, and repeat active
  passes until idle/no-active-work or explicit run-budget exhaustion. It also
  proves cooperative green yield requeues the running task, clears the current
  slot only after requeue, and lets the next active pass run the yielded task.
  It also proves scheduler-owned green timer ticks decrement per-carrier budget
  and yield/requeue the current green task when the time slice expires.
  Active-carrier timer sweeps now prove the scheduler ticks only active green
  carriers and leaves inactive carrier work queued. The preemption-safepoint
  bridge now proves timer-interrupt and compiler-safepoint sources route
  through the active-carrier sweep, and that unknown sources are rejected
  without ticking or mutating carrier state.
  The scheduler timer-interrupt adapter now proves `VEC_TIMER` maps to the
  `timer_interrupt` source, requires EOI acknowledgement, and reuses the same
  active-carrier preemption evidence.
  Named runtime and compiler safepoint adapters now prove future runtime poll
  sites and compiler-inserted checks have stable scheduler entrypoints without
  repeating source strings at call sites.
  The fixed-slot freestanding helper now proves a QEMU-friendly timer-slice
  yield path can requeue a running CPU1 green task without heap-heavy scheduler
  state. The live probe also constructs a scheduler-owned CPU1 carrier queue,
  dispatches task `701` through `Scheduler.run_green_carrier_once`, records one
  CPU1 green context switch, and verifies the normal OS CPU1 task slot remains
  `0`.
