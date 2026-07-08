<!-- codex-design -->
# Architecture: Scheduler + Process Isolation

## Decision

Use a class-based SMP scheduler core with per-CPU run queues and fair/background execution by default. Carry RT/deadline metadata end-to-end, and admit deadline tasks only through explicit runtime/period/deadline validation plus per-CPU bandwidth checks.

## Kernel Mechanism

- `TaskControlBlock` owns `TaskScheduleConfig` and `TaskIsolationProfile`.
- `SchedulerTopology` owns explicit scheduler domains. `Scheduler.new()`
  consumes boot-registered topology data when the architecture layer provides
  it, and otherwise falls back to a single flat domain over the configured
  logical CPU catalog. Domain kind and placement thresholds remain typed so
  SMT/cache/NUMA domains do not change scheduler APIs.
- `CpuRunQueue` owns class lanes: admitted deadline, RT metadata, fair, background, idle.
- Scheduler pick order is admitted deadline, fixed-priority RT, fair, background, idle. Direct metadata-only deadline activation remains rejected; admission uses the dedicated schedctl operation.
- Deadline admission rejects invalid budget tuples and per-CPU overload, then picks by earliest absolute virtual deadline.
- RT selection uses static priority within the RT lane and preserves queue order for equal priorities.
- Fair/background selection uses eligible virtual-deadline ordering and weighted virtual-runtime accounting on timer ticks.
- Per-CPU scheduling is exposed through `schedule_on_cpu`; the compatibility `schedule` path dispatches on CPU 0.
- Wake placement uses a wake-affine helper: a just-unblocked task prefers the
  current CPU when affinity allows it and the current CPU is within the
  topology wake threshold of the task's home CPU; otherwise it stays on its
  home CPU or the least-loaded affinity-compatible CPU.
- `rebalance_once` provides the topology-balancing primitive by moving a fair/background task from the busiest run queue to an affinity-compatible idle/low-load CPU.
- Timer/preemption and unblock paths call a conservative rebalance hook only
  when runnable-count spread reaches the topology rebalance threshold.

## Process Isolation

- User tasks initialize isolation metadata from their address-space id.
- Kernel tasks and cloned tasks initialize explicit isolation profiles instead of relying on implicit defaults.
- Capability records continue to be initialized on every task creation path.
- `sys_schedctl` exposes privileged isolation queries and monotonic restriction updates for per-task capability generation, sandbox state, network allowance, memory-page cap, thread cap, and address-space id.
- `pledge` and `unveil` continue to self-restrict the current task and advance the same isolation generation counter.

## Language Integration

- `@task` parses policy, weight, priority, latency hints, and budget fields.
- Validation requires RT/deadline policies to use `nogc_async_mut_noalloc` and rejects GC/allocation/unbounded blocking effects.

## Current Coverage And Remaining Work

> **The source paths below are implemented but not reachable at runtime — see
> "Runtime Integration Status" at the end of this document.**

Implemented source paths:

- `src/os/kernel/scheduler/scheduler.spl`: per-CPU class run queues, deadline admission, RT/fair/background/idle class pick order, fork/exec/wait collection, isolation metadata, and address-space release on exec/reap.
- `src/os/kernel/ipc/syscall.spl`: syscall dispatch for `fork`, `execve`, `waitpid`, `fcntl`, `poll`, scheduler policy control, and SOSIX sharing.
- `src/os/posix/fd_table.spl`: fork descriptor inheritance and close-on-exec state.
- `src/os/sosix/process.spl`: Simple-native async process facade used by POSIX process wrappers.

The first production slice is intentionally bounded. Remaining scheduler/process logic is:

- Prove automatic AP startup on a live SMP boot lane. MADT APIC IDs now feed
  both scheduler topology and per-CPU firmware metadata, `X86Interrupt.init()`
  calls the idempotent x86_64 AP startup hook after IDT/APIC init, and the
  low-memory AP trampoline marks APs online only after its 64-bit entry calls
  the AP-side online hook.
- Add non-x86 topology providers for ARM/RISC-V package or NUMA data where the
  platform exposes it.
- Extend fair scheduling from EEVDF-like virtual-deadline selection to full lag/sleeper decay and wakeup-preemption behavior.
- Add RT bandwidth throttling and priority-inheritance mutex integration before exposing unrestricted RT policy to user workloads.
- Extend deadline scheduling with CBS replenishment, deadline-miss accounting, and tracing.
- Harden `execve` copy-in with the future page-table walker once VMM exposes it. `syscall.spl` now copies optional argv/envp `char**` vectors with bounded user pointer validation, vector termination detection, argument count caps, and aggregate string byte caps before calling `build_user_process_image`; null vectors still preserve the legacy argv0-from-path behavior.
- Add process-group/session/stopped/continued semantics if full POSIX job-control compatibility is required.

## Runtime Integration Status (2026-07-08)

The scheduler design above is genuinely implemented — this is not vaporware.
`src/os/kernel/scheduler/*.spl` totals **4,850 lines** (verified `wc -l`,
2026-07-08) across 17 files: multiclass SMP pick order, deadline admission,
COW fork (`vmm_cow_clone_pages(parent.address_space)` at
`scheduler_exec.spl:298`), per-process address-space roots
(`address_space: user_as.phys_root` / `child_as` at `scheduler_exec.spl:212`,
`:263`, `:314`), and inline-asm context-switch (`context_switch.spl`,
160 lines). Give it credit as real kernel-grade code.

**However, none of it is triggered at runtime.** Two independent gaps combine
to leave the scheduler dead in the booted image:

1. **No return-to-scheduler / handoff bypass.** The generic
   `fs_exec_spawn` path returns a phantom pid and never maps PT_LOADs or
   enters ring-3. The one path that *does* reach ring-3,
   `x86_64_fs_exec_enter_image_ring3` in
   `src/os/kernel/loader/x86_64_fs_exec_ring3.spl:270`, calls
   `arch_x86_64_enter_user_task(ctx, space.phys_root)` at line 367 and
   iretq's directly to CPL3 — that file has **zero references to the
   scheduler**, and its own docstring (lines 273-274) states: "Does not
   return on success (the program runs at CPL3 and exits QEMU)." The
   process's own exit path triggers the QEMU `isa-debug-exit` device
   directly instead of trapping back into a kernel exit handler that
   resumes the scheduler. Either way — phantom pid or single-shot
   ring-3 — the scheduler never sees a real task through to completion.
2. **No per-process kernel stack.** `TaskControlBlock.kernel_stack` is
   hardcoded `0` at every task-creation site:
   `scheduler_task_mgmt.spl:80`, `scheduler_exec.spl:212` and `:263`,
   `scheduler_arm_bootstrap.spl:127` (fork's child inherits
   `parent.kernel_stack` at `scheduler_exec.spl:314`, so it stays 0
   transitively). There is no kernel-stack allocator and nothing sets
   `TSS.RSP0` on switch, so a real preemption or nested-syscall trap
   into this scheduler has nowhere safe to land.
3. **Timer IRQ is not wired to the scheduler.** On RISC-V64 the hook is
   literally commented out: `# scheduler_tick()` inside
   `rv64_handle_timer_interrupt()` at `src/os/kernel/arch/riscv64/timer.spl:166`.
   On x86_64, `src/os/kernel/arch/x86_64/timer.spl` (395 lines of
   APIC/TSC/HPET/PMTMR calibration) has **no scheduler/tick hook at
   all — not even a commented-out stub**. No architecture's timer
   interrupt calls into `scheduler.timer_tick`, so there is no
   preemptive multitasking anywhere in the tree today.

Net effect: this scheduler is implemented-but-unwired. It is dead at
runtime until the FS-exec keystone (M1 in the capability audit) runs one
real ring-3 process and returns control to the scheduler on exit instead
of exiting QEMU.

See also:

- `doc/03_plan/agent_tasks/simpleos_missing_os_subsystems_report.md` — the
  code-grounded capability audit this status section is drawn from.
- `doc/02_requirements/os/simpleos/simpleos_os_subsystem_feature_requests.md`
  — the M2 return-to-scheduler track: **FR-SOS-036** (process exit returns
  to the in-kernel exec caller via scheduler resume, retiring `out 0xf4`),
  **FR-SOS-038** (a CPL3 fault kills only the faulting task), **FR-SOS-039**
  (a timer tick taken at CPL3 is handled and resumes the ring-3 task).
