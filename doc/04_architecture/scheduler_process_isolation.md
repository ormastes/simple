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

Implemented source paths:

- `src/os/kernel/scheduler/scheduler.spl`: per-CPU class run queues, deadline admission, RT/fair/background/idle class pick order, fork/exec/wait collection, isolation metadata, and address-space release on exec/reap.
- `src/os/kernel/ipc/syscall.spl`: syscall dispatch for `fork`, `execve`, `waitpid`, `fcntl`, `poll`, scheduler policy control, and SOSIX sharing.
- `src/os/posix/fd_table.spl`: fork descriptor inheritance and close-on-exec state.
- `src/os/sosix/process.spl`: Simple-native async process facade used by POSIX process wrappers.

The first production slice is intentionally bounded. Remaining scheduler/process logic is:

- Extend x86_64 topology discovery from the current CPUID BSP shape plus online
  CPU count to full MADT/AP bring-up APIC ID enumeration.
- Add non-x86 topology providers for ARM/RISC-V package or NUMA data where the
  platform exposes it.
- Extend fair scheduling from EEVDF-like virtual-deadline selection to full lag/sleeper decay and wakeup-preemption behavior.
- Add RT bandwidth throttling and priority-inheritance mutex integration before exposing unrestricted RT policy to user workloads.
- Extend deadline scheduling with CBS replenishment, deadline-miss accounting, and tracing.
- Harden `execve` copy-in with the future page-table walker once VMM exposes it. `syscall.spl` now copies optional argv/envp `char**` vectors with bounded user pointer validation, vector termination detection, argument count caps, and aggregate string byte caps before calling `build_user_process_image`; null vectors still preserve the legacy argv0-from-path behavior.
- Add process-group/session/stopped/continued semantics if full POSIX job-control compatibility is required.
