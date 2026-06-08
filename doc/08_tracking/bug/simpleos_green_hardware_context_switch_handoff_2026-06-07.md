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
`[green-carrier-qemu] SCHED_HANDOFF_PASS=true` or the non-final
`[green-carrier-qemu] USER_HANDOFF_READY=true` /
`[green-carrier-qemu] USER_ENTRY_BRIDGE_READY=true` /
`[green-carrier-qemu] USER_SYSCALL_BRIDGE_READY=true` prerequisite markers.

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
- `src/os/kernel/arch/x86_64/user_entry_validation.spl`
  - `validate_enter_user_blocking_handoff`
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
- `test/01_unit/os/kernel/arch/x86_64_user_entry_validation_spec.spl`
  - current non-entering syscall-14 validation proof for missing and valid
    x86_64 user handoff records.
- `examples/09_embedded/simple_os/arch/x86_64/green_carrier_probe_entry.spl`
  - current live guest probe entry.

## Current Boundary

Do not mark `FR-RUNTIME-MULTICORE-GREEN-2026-06-06` done while this blocker is
open. The feature can claim hosted runtime-pool M:N evidence, cooperative-green
semantics, SimpleOS hosted scheduler evidence, and live QEMU AP scheduler-owned
handoff evidence, but not final SimpleOS ring/user hardware context-switch
handoff.

The Pure Simple scheduler handoff compatibility contract is now covered by
`test/01_unit/os/kernel/scheduler/scheduler_green_user_handoff_spec.spl` and
`test/01_unit/os/kernel/arch/x86_64_user_entry_validation_spec.spl`: they
dispatch a seeded user-task pid through the green lane, verify the same pid
still resolves to a `user_context`, and validate syscall-14 handoff readiness
without executing the ring transition. This is necessary setup evidence only;
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

## 2026-06-08 EnterUserBlocking Validation Boundary

`src/os/kernel/arch/x86_64/user_entry_validation.spl` now exposes
`validate_enter_user_blocking_handoff(pid_hint, scheduler)` as a non-entering
validation boundary for syscall `14`. The real `dispatch_enter_user_blocking`
path uses the same validation before calling `arch_x86_64_enter_user_task`.
Hosted and Docker specs can import the validation module without importing the
unsafe architecture enter bridge.

Docker evidence still keeps the current boundary honest:

- `simple check src/os/kernel/arch/x86_64/user_entry_validation.spl
  src/os/kernel/arch/x86_64/user_entry.spl
  test/01_unit/os/kernel/scheduler/scheduler_green_user_handoff_spec.spl`
  passes in `simple-test-isolation`.
- `simple test test/01_unit/os/kernel/scheduler/scheduler_green_user_handoff_spec.spl
  --mode=interpreter --clean` passes in `simple-test-isolation`.

This is prerequisite evidence only. It does not print or satisfy the final live
QEMU markers.

## 2026-06-08 Hosted Real-Spawn Handoff Prerequisite Fix

The hosted real-spawn prerequisite now has Docker-isolated evidence. ARM64
hosted/interpreter user-address-space and direct-load runtime symbols now have
non-baremetal stubs, so `Scheduler.create_user_task_pid(image,
TaskPriority.Normal, CapabilitySet.full())` can create a validation-ready TCB
from real `build_user_process_image` output instead of requiring manual TCB
seeding.

Passing evidence in `simple-test-isolation`:

- `test/01_unit/os/kernel/arch/x86_64_user_entry_validation_spec.spl`
  now has three scenarios: missing handoff rejection, real scheduler user-task
  creation through `create_user_task_pid`, and non-entering syscall-14
  validation of that real spawned handoff record.
- `test/01_unit/os/kernel/scheduler/scheduler_green_user_handoff_spec.spl`
  now dispatches the real spawned pid through `run_green_carrier_once` and then
  validates syscall-14 handoff readiness.

This closes the hosted real-spawn prerequisite, but not the final marker
triplet. The next step is to wire equivalent payload/address-space construction
into the live green-carrier guest before claiming `HW_HANDOFF_PASS=true`,
`USER_ENTRY_PASS=true`, or `USER_SYSCALL_PASS=true`.

## 2026-06-08 Guest User Handoff Readiness Prerequisite

The live green-carrier guest probe now has a non-final
`USER_HANDOFF_READY=true` marker. The marker is emitted only after the guest
constructs an in-memory x86_64 user payload image, creates a scheduler user
task through `create_user_task_pid`, dispatches that pid through
`run_green_carrier_once` on CPU1, and validates syscall-14 handoff readiness through
`validate_enter_user_blocking_handoff`.

This is still prerequisite evidence only. It proves guest-side payload,
scheduler task, green-lane dispatch, and non-entering user handoff validation
can compose in the live AP probe. It does not execute `rt_x86_enter_user_first`,
does not enter user mode, and does not observe a user-mode syscall return.
The final live gate still requires `HW_HANDOFF_PASS=true`,
`USER_ENTRY_PASS=true`, and `USER_SYSCALL_PASS=true` from the real AP ring/user
path.

## 2026-06-08 Guest User Entry Bridge Readiness Prerequisite

The live green-carrier guest probe now emits non-final
`USER_ENTRY_BRIDGE_READY=true` only after installing the x86_64 trap runtime,
calling `install_syscall_entry()`, checking `syscall_entry_installed()`, and
resolving a nonzero `kernel_syscall_entry_asm` address through
`kernel_syscall_entry_addr()`.

This closes the live entry-bridge arming prerequisite, but not the final marker
triplet. The probe still must drive the real AP ring/user path and observe
`HW_HANDOFF_PASS=true`, `USER_ENTRY_PASS=true`, and `USER_SYSCALL_PASS=true`
before this bug can close.

## 2026-06-08 Guest User Syscall Bridge Readiness Prerequisite

The live green-carrier guest probe now emits non-final
`USER_SYSCALL_BRIDGE_READY=true` only after initializing the
`os.kernel.abi.syscall_shim` keepalive path and dispatching syscall 60
`debug_write` through the strong `spl_handle_debug_write` override.

This closes the live kernel-side syscall shim prerequisite, but not the final
marker triplet. The probe still must enter ring 3 and observe a user-mode
payload issue and return from a syscall before it may print
`USER_SYSCALL_PASS=true`.

## 2026-06-08 Direct Final-Entry Probe Finding

A direct final-entry experiment created an in-memory ring-3 payload that would
issue syscall 60 `debug_write` for the final marker triplet, then attempted to
enter it through `dispatch_enter_user_blocking` after the CPU1 green-carrier
dispatch. Without a real VMM bootstrap, the non-entering validation still
reported a legacy `cr3=1` address-space sentinel. Entering that path did not
reach the user payload and did not emit `HW_HANDOFF_PASS=true`,
`USER_ENTRY_PASS=true`, or `USER_SYSCALL_PASS=true`.

A follow-up attempt to initialize PMM/VMM inside
`green_carrier_probe_entry.spl` stopped before PMM returned, even after moving
the scalar PMM bitmap away from stale guessed kernel bounds. The built probe's
ELF showed `_kernel_end` near `0x0ecef000`, proving the old `0x01400000`
reserved-end guess was invalid for this entry. The failure mode is now sharper:
the final path needs a safe direct-boot memory bootstrap or a dedicated minimal
user page-table allocator before it can replace the legacy `cr3=1` sentinel.

Do not merge a final-marker payload into the default live probe until this
memory-bootstrap gap is closed. The readiness probe must remain able to pass
without printing or attempting the final marker triplet.
