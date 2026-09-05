<!-- codex-research -->
# Local Research: Scheduler + Process Isolation

Date: 2026-04-20

## Existing State

- `src/os/kernel/scheduler/scheduler.spl` had a single scheduler instance with fixed priority queues and round-robin slices.
- `src/os/kernel/smp/percpu.spl` already defined per-CPU state and reserved a runqueue length field, but the scheduler did not yet own per-CPU run queues.
- `src/os/kernel/types/task_types.spl` carried task state, priority, address-space root, parent, and context fields, but not scheduler policy metadata or isolation profiles.
- `src/os/kernel/ipc/syscall.spl` reserved `sys_schedule = 106` and `sys_schedctl = 107` in architecture docs, but dispatch handlers were missing.
- Existing syscall handlers called `Scheduler.set_priority()` and `tick_count()`, while the scheduler only exposed `get_tick_count()`.
- Runtime-family docs identify `nogc_async_mut_noalloc` as the no-heap baremetal/RT-capable family and document current enforcement gaps.

## Implementation Direction

V1 should keep the kernel scheduler as the mechanism owner, with userland `SchedService` remaining advisory policy. Process isolation stays in the SimpleOS kernel path: address spaces, capability records, pledge/unveil, parent/child lifecycle, and scheduler policy metadata.

## Key Risks

- Full EDF/CBS deadline execution would overrun the current scheduler scaffolding, so v1 stores/rejects deadline metadata until admission and runtime accounting are designed.
- Existing tests rely on `create_task()` creating runnable tasks; implementation must restore that contract.
