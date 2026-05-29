# SimpleOS FR-SOS-024 Phase 3 — x86_64 Ring-3 First-Dispatch Design

## Status

Phase 3 partial — implemented. Sibling phases:

- Phase 1 (diagnosis) — `doc/08_tracking/bug/syscall13_enqueue_stall_2026-04-21.md`.
- Phase 2 (bulk-copy fix) — committed 2026-04-21 as `9e62c438`.
- Desktop-lane compositor fault — workaround committed 2026-04-21 as `857f9f42`.

Commits that landed Phase 3 partial (all on main):

- `4708c2c9` — `arch_x86_64_enter_user_first` ring-3 first-dispatch helper
- `70b86c97` — scheduler enqueue path unblocked for user tasks
- `df557a44` — VMM init sentinel (`g_vmm_initialized` → `u64` sentinel)
- `fe81b853` — VMM gate on `g_vmm.pml4_phys` instead of init flag
- `a0e65c3b` — module counter `g_user_task_next_pid` for user-task PIDs
- `a3f4f666` — launcher scanner fix + scheduler module global + syscall 14
  (EnterUserBlocking) wired end-to-end

Pre-blocker x86_64 desktop disk live result: Browser Demo pid=1, Hello World
pid=2, Editor pid=3, `mode=filesystem-process`, `editor-save:ok`,
`cli-verify:ok`, `TEST PASSED`, 0 faults.

Full live re-verification is blocked by a compiler freestanding-stub
symbol-weakness collision tracked in
`doc/08_tracking/todo/simpleos_stub_collision_freestanding_2026-04-21.md`.
Once that compiler fix lands, the syscall 13 gate at
`src/os/kernel/ipc/syscall.spl:1246` can be lifted and the live evidence
re-confirmed.

## Goal

Make a scheduler-owned user task created by `scheduler.create_user_task`
actually execute at ring 3 on x86_64. Close FR-SOS-024 acceptance
criterion 3 ("the x86_64 trap-return or scheduler path can switch into
the new task's `user_context` and return to ring 3").

## Current State

What already exists:

- `scheduler.create_user_task(image, priority, caps)` builds a TCB
  with `is_user: true`, a user-mode `X86ContextSwitch.create(entry,
  user_sp, user_mode=true)` that sets `cs = GDT_USER_CS | 3` and
  `ss = GDT_USER_DS | 3`, and an `address_space: user_as.phys_root`.
- `scheduler/context_switch.spl:54-95` has a `context_restore(ctx)`
  that builds an `iretq` frame on the stack and does the `iretq`.
  It pushes `ss, rsp, rflags, cs, rip` in the correct order, so it
  will transition to ring 3 iff `cs` already has RPL 3 (it does for
  user tasks).
- `scheduler/scheduler.spl:780` has `schedule_on_cpu(cpu_id)` that
  picks the next task and returns its `TaskContext`.
- x86_64 GDT has `GDT_USER_CODE = 0x18` / `GDT_USER_DATA = 0x20` and
  a TSS slot at `GDT_TSS = 0x28` (`src/os/kernel/arch/x86_64/gdt.spl`).
- Recent commit `9e62c438` made the ELF segment mapping fast enough
  that `create_user_task` no longer times out during `map_all`.

What is missing:

- **Nothing in x86_64 actually drives the scheduler.** Nobody calls
  `scheduler.schedule()` or `scheduler.schedule_on_cpu()` in the
  desktop E2E boot path. The TCB is built, enqueued, and then never
  picked up. The kernel stays in the single linear `spl_start`
  control flow throughout.
- **CR3 is never switched to the user task's address space.** The
  TCB records `address_space: user_as.phys_root`, but
  `context_restore` only manipulates GPRs and does `iretq`. With CR3
  still pointing at the kernel PML4, the iretq to `cs | 3` would
  either fault immediately (user `cs` not accessible) or execute
  kernel memory as user code.
- **TSS.RSP0 is never set to a per-task kernel stack.** The first
  ring-3 → ring-0 transition (next syscall or trap from the user
  task) needs RSP0 loaded with a valid kernel stack. If it holds 0
  or garbage, the first interrupt from ring 3 triple-faults.
- **The `syscall`/`sysret` MSRs (STAR, LSTAR, SFMASK) are never
  initialized.** User-mode `syscall` instructions would #GP. The
  kernel currently dispatches syscalls through `int 0x80` (or a C
  stub) from its own ring-0 code — not through a ring-3 `syscall`
  trap. Either wire the MSRs and the syscall handler entry, or fall
  back to a software-interrupt syscall ABI (`int 0x80`).
- **Syscall 13 is not reached from the baremetal path today.** Even
  with the `-12` gate at `src/os/kernel/ipc/syscall.spl:1246`
  removed, `posix_spawn_with_args` returns 0 without emitting any
  `[syscall13]` marker — the launcher falls through to the
  resident-manifest path. Either `syscall_raw.syscall()`
  (`src/os/userlib/syscall_raw.spl:9`, which uses the x86_64
  `syscall` instruction in ring 0) is being intercepted or silently
  stubbed, or the syscall trap entry is unhooked in the baremetal
  lane. See "Routing investigation" below.

## Recommended Approach

Minimal MVP: a direct, non-preemptive hand-off. Build the
long-running scheduler loop in a later phase.

### 1. Syscall entry fix (investigate first)

Before touching ring-3 code, prove that the baremetal lane can
actually observe a syscall. Symptoms: lifting the Phase-2 gate
should have made `[syscall13] dispatch_direct enter` fire under
`posix_spawn`, but it didn't. Suspects:

- **LSTAR / STAR / SFMASK MSRs never written.** In 64-bit mode the
  `syscall` instruction traps to the LSTAR MSR. If the kernel
  never writes those, `syscall` from ring 0 is a no-op or a #UD.
  Check `src/os/kernel/arch/x86_64/arch_init.spl` and
  `cpu.spl` — look for `IA32_STAR`/`IA32_LSTAR`/`IA32_FMASK` MSR
  writes. Likely missing.
- **Syscall dispatcher export.** The runtime expects
  `spl_handle_*` C-ABI exports from `os.kernel.abi.syscall_shim`,
  which overlays weak `-ENOSYS` stubs from `baremetal_stubs.c`.
  If the syscall shim module isn't in the build graph (check the
  `use` tree from `desktop_e2e_entry.spl`), the weak stubs win
  and everything returns `-ENOSYS == -38`, not `-12`.
- **The `syscall` instruction never traps in baremetal ring-0
  code.** On some CPU configurations, `syscall` from CPL=0 is a
  #UD. If the rich fault handler swallows that (recovery path),
  the caller sees whatever was in RAX at the time — often 0.
  Verify by adding a serial marker immediately after the
  `syscall` instruction: if we never see it, the instruction is
  not returning (recovered past it via fault handler).

Fix: enable STAR/LSTAR/SFMASK + TSS.RSP0 before any syscall
attempt; confirm `[syscall13] dispatch_direct enter` fires on the
live lane.

### 2. Ring-3 first-dispatch helper

Add `arch_x86_64_enter_user_first(ctx: TaskContext, cr3: u64,
kernel_rsp0: u64)` in `src/os/kernel/arch/x86_64/context.spl`.
Semantics:

1. Load `cr3` with the user task's PML4 physical address.
2. Store `kernel_rsp0` at TSS.RSP0 (`GDT_TSS` descriptor).
3. Build the `iretq` frame using the existing
   `scheduler/context_switch.spl:54-95` pattern
   (`push ss, rsp, rflags, cs, rip`) — but from the per-task
   `user_context`, not the kernel context.
4. `iretq`.
5. Does not return.

This is basically `context_restore` plus CR3 and TSS.RSP0 writes,
wrapped as a public entry point.

### 3. Call site

In `src/os/kernel/ipc/syscall.spl`, extend
`_spawn_from_resolved_bytes` to optionally enter the new task
directly instead of returning its PID to the caller. Two variants:

- **Blocking spawn (MVP):** after
  `sched.create_user_task(image_result.unwrap(), priority,
  caps)`, resolve the task's `user_context` and address space and
  call `arch_x86_64_enter_user_first(...)`. Does not return. When
  the user task calls `exit`, the kernel's exit syscall handler
  takes over and can return to whatever would have been the
  spawn's next instruction — but that requires threading kernel
  state back through the trap return path.
- **Scheduler-backed spawn (better):** the PID-returning variant
  the original code already has, plus a trip through a cooperative
  "run this task now" primitive. The first time the scheduler
  sees a task with `is_user == true && state == Ready &&
  user_context == Some(...)`, it invokes
  `arch_x86_64_enter_user_first`. This needs the scheduler loop
  (below).

### 4. Scheduler loop (follow-up)

For full FR-SOS-024 close, the kernel needs a real scheduler
driver: timer interrupt → `scheduler.timer_tick(ctx)` → picked
next task → `context_restore(next_ctx)`. Currently there is no
loop. Options:

- **APIC timer:** the recent `aee87bd9` / `5a6482d3` commits
  staged APIC and AP-trampoline infrastructure. Wiring APIC timer
  to call `timer_tick` would give preemption.
- **PIT as a stopgap:** simpler but legacy; good enough for
  single-CPU baremetal tests.

Without this loop, user tasks can only run cooperatively (they
must `exit` or `yield` to return control). Acceptable for the
"load a hello-world ELF and have it call `exit(0)`" milestone.

### 5. ELF segment copy

Already done in Phase 2 (`9e62c438`). Re-verify with a live run
once routing is fixed.

### 6. GDT/TSS dependencies

Double-check:

- `GDT_USER_CS` and `GDT_USER_DS` are installed at DPL 3 (not
  only the selector value — the descriptor's DPL field too).
- The TSS descriptor is loaded with `LTR`. Look for an `ltr`
  instruction in `src/os/kernel/arch/x86_64/cpu.spl` or
  `arch_init.spl`.
- `IA32_EFER.SCE` (System Call Extension) bit is set, otherwise
  the `syscall` instruction is #UD.

## Acceptance

Minimum evidence the phase has landed:

1. `[syscall13] dispatch_direct enter` reappears in the desktop
   disk serial log (routing fix).
2. `[syscall13] user image handoff ok` (Phase 2 code, lifted
   gate) appears.
3. A hello-world user ELF from `/sys/apps/hello_world` writes a
   known byte to the serial port *from ring 3* and then calls
   `exit(0)`. The ring-3 write proves the transition succeeded;
   the `exit(0)` proves the syscall return path works.
4. No `[fault] *** EXCEPTION FRAME ***` entries in the lane.
5. Desktop E2E still reaches `TEST PASSED`.

## Out of scope

- Dynamic linking / `.so` support.
- Demand paging / page-fault handler for lazy ELF loading.
- Non-x86_64 arches (riscv64 has `_rv64_enter_user` as a
  reference model but is a separate lane).
- Multi-process isolation beyond the first user task.
- User signals.

## References

- FR-SOS-024: `doc/08_tracking/feature_request/simpleos_os_requests.md`
- Phase 2 commit `9e62c438`: bulk ELF segment copy.
- Phase 1 diagnosis:
  `doc/08_tracking/bug/syscall13_enqueue_stall_2026-04-21.md`
- Desktop-lane compositor workaround:
  `doc/08_tracking/bug/simpleos_desktop_lane_mouse_compositor_fault_2026-04-21.md`
- `src/os/kernel/arch/riscv64/trap_vector.S:230` — `_rv64_enter_user`
  is the architectural reference pattern.
- `src/os/kernel/scheduler/context_switch.spl:54-95` — existing
  `iretq` frame builder to reuse.
