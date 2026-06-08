# SimpleOS Multicore Green Evidence - 2026-06-07

## Scope

This report records the SimpleOS evidence for the multicore-green SPipe lane,
including the opt-in live QEMU green-carrier proof. It does not claim final
ring/user context-switch handoff across APs; the live proof covers AP startup,
fixed-slot CPU1 green dispatch/IPI evidence, fixed timer-preemption yield
evidence, scheduler-owned CPU1 green handoff through the real `Scheduler`, and
non-final scheduler/user handoff readiness through `USER_HANDOFF_READY=true`.
The final hardware handoff gap is tracked in
`doc/08_tracking/bug/simpleos_green_hardware_context_switch_handoff_2026-06-07.md`.

## Verified Commands

Commands were refreshed from `/tmp/simple-pherallel-sync` after initializing
the `examples/09_embedded/simple_os` submodule.

```sh
./src/compiler_rust/target/debug/simple test test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl --mode=interpreter --clean
./src/compiler_rust/target/debug/simple test test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl --mode=interpreter --clean
./src/compiler_rust/target/debug/simple test test/03_system/os/simpleos/feature/simpleos_green_channel_wake_spec.spl --mode=interpreter --clean
./src/compiler_rust/target/debug/simple test test/03_system/os/simpleos/feature/simpleos_green_hardware_handoff_blocker_spec.spl --mode=interpreter --clean
./src/compiler_rust/target/debug/simple check src/os/kernel/scheduler/green_carrier.spl
./src/compiler_rust/target/debug/simple test test/01_unit/os/kernel/scheduler/green_carrier_spec.spl --mode=interpreter --clean
./src/compiler_rust/target/debug/simple check src/os/kernel/scheduler/scheduler.spl
./src/compiler_rust/target/debug/simple test test/01_unit/os/kernel/scheduler/scheduler_green_parallelism_spec.spl --mode=interpreter --clean
./src/compiler_rust/target/debug/simple test test/01_unit/os/kernel/scheduler/scheduler_green_user_handoff_spec.spl --mode=interpreter --clean
./src/compiler_rust/target/debug/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean
SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1 bin/release/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean
# Future final hardware gate, expected to remain opt-in until all final markers
# exist: HW_HANDOFF_PASS, USER_ENTRY_PASS, and USER_SYSCALL_PASS.
# SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1 bin/release/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean
```

## Results

| Evidence | Result | Assertions |
|----------|--------|------------|
| SimpleOS cooperative green | PASS | 3 |
| SimpleOS multicore green scheduler contract | PASS | 6 |
| SimpleOS green-channel wake bridge | PASS | 4 |
| SimpleOS final hardware handoff blocker contract | PASS | 3 |
| SimpleOS green-carrier compile check | PASS | 1 file |
| SimpleOS green-carrier unit contract | PASS | 38 |
| SimpleOS scheduler compile check | PASS | 1 file |
| SimpleOS scheduler green-carrier parallelism | PASS | 29 |
| SimpleOS scheduler green/user handoff compatibility | PASS | 1 |
| SimpleOS green-carrier QEMU spec default lane | PASS | 2 |
| SimpleOS green-carrier QEMU live lane | PASS | 2 |

## Current Refresh

After syncing `/tmp/simple-pherallel-sync` to `origin/main` at `9b5cb43402`,
the SimpleOS green-thread loop was rerun with `--clean` on 2026-06-07. The
direct rerun passed:

- cooperative green system contract: 3 assertions
- multicore green scheduler contract: 6 assertions
- green-channel wake bridge: 4 assertions
- green-carrier compile check: 1 file
- green-carrier unit contract: 38 assertions
- scheduler compile check: 1 file
- scheduler green-carrier parallelism: 29 assertions
- QEMU default gate lane: 1 assertion
- QEMU live lane: 1 assertion in 37645ms

After syncing `/tmp/simple-pherallel-sync` to `origin/main` at `989e782de4`,
the blocker contract and QEMU green-carrier lanes were rerun:

- final hardware handoff blocker contract: 2 assertions
- QEMU default gate lane: 2 assertions
- QEMU live lane: 2 assertions in 40588ms

After syncing `/tmp/simple-pherallel-sync` to `origin/main` at `f91f76ecb2`,
the scheduler green/user handoff compatibility spec was added and run:

- scheduler green/user handoff compatibility: 1 assertion group in 7156ms

After syncing `/tmp/simple-pherallel-sync` to `origin/main` at `ac44a12ffd`,
the final hardware handoff gate was rerun after adding the requirements/report
alignment scenario:

- final hardware handoff blocker contract: 3 scenarios
- QEMU default gate lane: 2 scenarios
- final live hardware handoff lane remains opt-in and unclaimed until the guest
  emits hardware handoff, user-entry, and user-syscall markers from the real
  AP ring/user path

This refresh does not claim final ring/user context-switch handoff across APs;
that claim remains blocked by
`doc/08_tracking/bug/simpleos_green_hardware_context_switch_handoff_2026-06-07.md`.

After syncing `/tmp/simple-pherallel-sync` to `origin/main` at `30e5b3a9fd`,
the SimpleOS submodule was advanced to `f8d3554` with a freestanding x86_64
`rt_string_char_code_at` implementation. The previously observed native-build
link blocker is closed:

- final hardware handoff blocker contract: PASS, 3 scenarios in 98ms
- `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1` live QEMU gate: PASS, 2 scenarios in
  37771ms
- `SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1` final-handoff QEMU gate:
  FAIL as the remaining expected final-marker blocker, 1 passed scenario and 1
  failed scenario in 37998ms
- the final-handoff serial output includes AP startup, `PASS=true`,
  `PREEMPT_PASS=true`, and `SCHED_HANDOFF_PASS=true`
- the final-handoff serial output still lacks `HW_HANDOFF_PASS=true`,
  `USER_ENTRY_PASS=true`, and `USER_SYSCALL_PASS=true`

After the x86_64 user selector refresh, the scheduler/user handoff setup now
uses the boot GDT's 64-bit user code selector (`CS=0x2B`, `SS=0x23`) instead
of the compat selector. Rerun evidence:

- GDT layout contract: PASS, 7 scenarios
- scheduler green/user handoff compatibility: PASS, 1 scenario
- x86 boot selector usage contract: PASS, 22 scenarios
- x86_64 kernel MVP ring3 context smoke: PASS, 6 scenarios
- `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1` live QEMU gate: PASS, 2 scenarios in
  37223ms
- `SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1` final-handoff QEMU gate:
  FAIL as expected, 1 passed scenario and 1 failed scenario in 37480ms; serial
  still shows AP startup plus `SCHED_HANDOFF_PASS=true`, but no final
  hardware/user markers

After syncing `/tmp/simple-pherallel-sync` to `origin/main` at `faea65ef00`,
the green-carrier guest probe and QEMU spec were refreshed to include the
non-final `USER_HANDOFF_READY=true` readiness marker. Docker-isolated
verification on the default/non-live lane passed:

- `simple check examples/09_embedded/simple_os/arch/x86_64/green_carrier_probe_entry.spl
  test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl
  test/03_system/os/simpleos/feature/simpleos_green_hardware_handoff_blocker_spec.spl`:
  PASS, 3 files
- final hardware handoff blocker contract: PASS, 3 scenarios
- QEMU default gate lane: PASS, 2 scenarios
- generated-spec layout guard: `doc/06_spec/**/*_spec.spl` count `0`

The live QEMU readiness lane now requires serial output containing all current
readiness markers:

```text
[smp] AP reached 64-bit entry
[green-carrier-qemu] PASS=true
[green-carrier-qemu] PREEMPT_PASS=true
[green-carrier-qemu] SCHED_HANDOFF_PASS=true
[green-carrier-qemu] USER_HANDOFF_READY=true
```

`USER_HANDOFF_READY=true` is emitted only after the guest constructs an
in-memory x86_64 user payload image, creates a scheduler user task through
`create_user_task_pid`, dispatches that pid through the CPU1 green lane, and
validates the non-entering syscall-14 handoff record. It remains prerequisite
evidence only; it does not execute `rt_x86_enter_user_first`, enter user mode,
or observe a user-mode syscall return.

## Notes

- The default QEMU spec lane proves the opt-in gate is wired and disabled unless
  `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1` is set.
- The live lane passed in 40588ms on `989e782de4`. The spec built the x86_64
  probe, booted a two-CPU QEMU guest, and asserted
  `[smp] AP reached 64-bit entry`,
  `[green-carrier-qemu] PASS=true`, and
  `[green-carrier-qemu] PREEMPT_PASS=true`, and
  `[green-carrier-qemu] SCHED_HANDOFF_PASS=true` in serial output. Current
  live readiness evidence additionally requires
  `[green-carrier-qemu] USER_HANDOFF_READY=true`.
- The final AP ring/user hardware handoff markers are deliberately separate:
  `[green-carrier-qemu] HW_HANDOFF_PASS=true`,
  `[green-carrier-qemu] USER_ENTRY_PASS=true`, and
  `[green-carrier-qemu] USER_SYSCALL_PASS=true` are required only when
  `SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1` is set. A scheduler-only
  probe must not print any of those final markers.
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
