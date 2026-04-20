<!-- codex-design -->
# Architecture: Scheduler + Process Isolation

## Decision

Use a class-based SMP scheduler core with per-CPU run queues and fair/background execution in v1. Carry RT/deadline metadata end-to-end, but keep deadline disabled until admission control and CBS runtime accounting are implemented.

## Kernel Mechanism

- `TaskControlBlock` owns `TaskScheduleConfig` and `TaskIsolationProfile`.
- `CpuRunQueue` owns class lanes: deadline metadata, RT metadata, fair, background, idle.
- Scheduler pick order is deadline metadata lane, RT metadata lane, fair, background, idle. Deadline activation is rejected by syscall policy in v1.
- Fair/background selection uses eligible virtual-deadline ordering.

## Process Isolation

- User tasks initialize isolation metadata from their address-space id.
- Kernel tasks and cloned tasks initialize explicit isolation profiles instead of relying on implicit defaults.
- Capability records continue to be initialized on every task creation path.

## Language Integration

- `@task` parses policy, weight, priority, latency hints, and budget fields.
- Validation requires RT/deadline policies to use `nogc_async_mut_noalloc` and rejects GC/allocation/unbounded blocking effects.
