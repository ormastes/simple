# SimpleOS Multicore Green Evidence - 2026-06-07

## Scope

This report records the SimpleOS evidence for the multicore-green SPipe lane,
including the opt-in live QEMU green-carrier proof. It does not claim final
hardware context-switch handoff across APs; the live proof covers AP startup
plus scheduler-visible CPU1 green dispatch.

## Verified Commands

All commands were run from `/tmp/simple-cooperative-green`.

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
| SimpleOS multicore green scheduler contract | PASS | 3 |
| SimpleOS green-channel wake bridge | PASS | 4 |
| SimpleOS green-carrier compile check | PASS | 1 file |
| SimpleOS green-carrier unit contract | PASS | 36 |
| SimpleOS scheduler compile check | PASS | 1 file |
| SimpleOS scheduler green-carrier parallelism | PASS | 23 |
| SimpleOS green-carrier QEMU spec default lane | PASS | 1 |
| SimpleOS green-carrier QEMU live lane | PASS | 1 |

## Notes

- The default QEMU spec lane proves the opt-in gate is wired and disabled unless
  `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1` is set.
- The live lane passed in 40469ms. The spec built the x86_64 probe, booted a
  two-CPU QEMU guest, and asserted both `[smp] AP reached 64-bit entry` and
  `[green-carrier-qemu] PASS=true` in serial output.
- The hosted SimpleOS specs prove scheduler-owned green execution state remains
  separate from normal OS task state.
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
  carriers and leaves inactive carrier work queued.
