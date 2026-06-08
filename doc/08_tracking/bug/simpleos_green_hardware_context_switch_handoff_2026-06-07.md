# SimpleOS Green Hardware Context-Switch Handoff Blocker - 2026-06-07

## Summary

The multicore-green SimpleOS lane has hosted scheduler evidence and live QEMU AP
evidence, but it does not yet prove the final ring/user hardware context-switch
handoff across application processors.

Current live QEMU evidence proves:

- AP startup reaches the 64-bit entry marker.
- CPU1 fixed-slot green dispatch and IPI intent pass.
- CPU1 fixed timer-preemption yield and requeue pass.
- The real `Scheduler` accepts task `701` through
  `Scheduler.run_green_carrier_once`, records one CPU1 green context switch, and
  leaves the normal OS CPU1 task slot unchanged.

That is scheduler-owned green handoff evidence, not final hardware context
handoff evidence.

## Missing Proof

Before this blocker can close, a live guest must prove that a runnable green task
can cross the actual AP hardware context-switch boundary used by SimpleOS ring or
user task execution, rather than only updating hosted scheduler state and
QEMU-friendly fixed carrier slots.

Minimum evidence:

- the AP owns the runnable green task through the same scheduler queue state used
  by normal execution;
- the handoff reaches the real context-switch/trap-return path for the target AP;
- green task state and normal OS task state remain distinct after the handoff;
- timer or safepoint preemption can yield that AP-owned green task without
  corrupting the normal OS current-task slot;
- the live QEMU SSpec records named serial markers for the final hardware
  handoff, user entry, and user-mode syscall return.

## Verification Target

Extend `test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl` and
`examples/09_embedded/simple_os/arch/x86_64/green_carrier_probe_entry.spl` only
after the SimpleOS kernel path exposes the real AP context-switch proof point.
The final marker must be separate from the existing
`SCHED_HANDOFF_PASS=true` marker so scheduler-state evidence cannot be mistaken
for ring/user hardware handoff evidence.

Use separate final markers:
`[green-carrier-qemu] HW_HANDOFF_PASS=true`,
`[green-carrier-qemu] USER_ENTRY_PASS=true`, and
`[green-carrier-qemu] USER_SYSCALL_PASS=true`; do not overload
`[green-carrier-qemu] SCHED_HANDOFF_PASS=true`.

The executable live gate is
`SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1`. It should fail until the
guest probe prints all final hardware/user markers from a real AP ring/user
handoff path whose user payload reaches the syscall entry and returns through
the kernel syscall dispatcher.

Current proof-point candidates:

- `src/os/kernel/scheduler/context_switch.spl`
  - `context_restore`
  - `switch_context_with_as`
- `src/os/kernel/arch/x86_64/context.spl`
  - `arch_x86_64_enter_user_task`
  - `rt_x86_enter_user_first`
- `src/os/kernel/arch/x86_64/user_entry.spl`
  - `dispatch_enter_user_blocking`
- `src/os/kernel/arch/x86_64/cpu.spl`
  - `kernel_syscall_entry_asm`
  - `rt_syscall_dispatch`
- `src/os/kernel/ipc/syscall.spl`
  - `syscall_handler`
- `test/03_system/os/qemu/os/scheduler/context_switch_qemu_spec.spl`
  - existing QEMU context-switch lane, currently too broad to prove green AP
    ring/user handoff.
- `test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl`
  - current live AP green-carrier proof.
- `test/01_unit/os/kernel/scheduler/scheduler_green_user_handoff_spec.spl`
  - current Pure Simple scheduler/user-context compatibility proof before the
    architecture handoff bridge.
- `examples/09_embedded/simple_os/arch/x86_64/green_carrier_probe_entry.spl`
  - current live guest probe entry.

## Current Boundary

Do not mark `FR-RUNTIME-MULTICORE-GREEN-2026-06-06` done while this blocker is
open. The feature can claim hosted runtime-pool M:N evidence, cooperative-green
semantics, SimpleOS hosted scheduler evidence, and live QEMU AP scheduler-owned
handoff evidence, but not final SimpleOS ring/user hardware context-switch
handoff.

The Pure Simple scheduler handoff compatibility contract is now covered by
`test/01_unit/os/kernel/scheduler/scheduler_green_user_handoff_spec.spl`: it
dispatches a seeded user-task pid through the green lane and verifies the same
pid still resolves to a `user_context`. This is necessary setup evidence only;
the final blocker remains open until live QEMU observes the x86_64 user entry
and syscall-return path.

## 2026-06-07 Link Blocker Refresh

The SimpleOS freestanding x86_64 runtime now exports
`rt_string_char_code_at`, matching the hosted native raw-index/raw-code string
helper contract. That closes the native-build link blocker that previously
stopped the live final-handoff QEMU gate before boot.

With SimpleOS submodule commit `f8d3554`, the opt-in live gate builds and boots
the two-CPU guest. The scheduler-owned AP carrier proof still passes, including
`SCHED_HANDOFF_PASS=true`; the final lane remains open because the guest serial
does not yet print `HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, or
`USER_SYSCALL_PASS=true`.

## 2026-06-07 Final Marker Root Cause

The current green-carrier QEMU probe is a `qemu -kernel` guest with no mounted
user payload. Its scheduler handoff path seeds only scheduler-owned green state;
it does not create a real x86_64 user address space or call
`dispatch_enter_user_blocking`.

The existing real x86_64 user-entry route is disk/spawn based:
`desktop_e2e_entry.spl` mounts VFS, spawns `/sys/apps/ring3_smoke.smf`, then
calls syscall `14` (`EnterUserBlocking`) to reach `rt_x86_enter_user_first`.
That route can prove user entry/syscall return, but it is not wired into the
green-carrier `-kernel` probe and is not AP-green-affine yet.

Do not close this blocker by printing the final markers from scheduler code.
The next implementation step must either add a real direct in-memory user
payload/address-space probe to the green-carrier guest, or teach the opt-in
QEMU gate to boot the disk-backed ring3 smoke path and connect it to the
green-carrier AP handoff.

The x86_64 user-context selector setup is no longer a blocker: the scheduler
and `X86ContextSwitch.create(..., user_mode=true)` now use `CS=0x2B` and
`SS=0x23`, matching the boot GDT's 64-bit user code/data descriptors. The
remaining blocker is payload/CR3/user-entry wiring, not the selector frame.

## 2026-06-08 IPC Handoff Side-Blocker Fix

`test/01_unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl` now passes in a
separate Docker process. The IPC send syscall consumes the first waiting
receiver and calls the explicit CPU-aware scheduler unblock path, so the
waiter-consumption handoff no longer blocks the final AP/user proof.

This does not close the live SimpleOS hardware handoff blocker. The final QEMU
gate still must emit `HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, and
`USER_SYSCALL_PASS=true` from a real AP ring/user payload path.
