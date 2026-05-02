<!-- codex-design -->
# Detail Design: Scheduler + Process Isolation

## Data Structures

- `SchedulerPolicy`: `Internal`, `Fair`, `Background`, `RtFifo`, `RtRoundRobin`, `Deadline`, `Idle`.
- `TaskScheduleConfig`: policy metadata, fair accounting, deadline budget fields, affinity and home CPU.
- `TaskIsolationProfile`: address-space id, capability generation, sandbox defaults, resource caps.
- `CpuRunQueue`: per-class ready queues and local load counters.

## Algorithms

- Enqueue mirrors legacy priority queues and per-CPU class queues.
- `schedule_on_cpu(cpu)` picks from a normalized per-CPU queue; `schedule()` remains the CPU 0 compatibility path.
- Pick order is admitted deadline, fixed-priority RT, fair, background, idle.
- `admit_deadline` validates `runtime <= deadline <= period`, computes fixed-point utilization, chooses an affinity-compatible CPU under the bandwidth cap, and moves ready tasks into the deadline lane.
- Deadline lanes pick the task with the earliest absolute virtual deadline.
- RT lanes scan for the highest static priority, with FIFO/RR behavior preserved for equal priorities.
- Fair/background lanes pick the eligible task with the earliest virtual deadline.
- Timer ticks advance fair/background `vruntime`, recompute virtual deadline, and pay down positive lag.
- `rebalance_once()` moves one fair/background task from the busiest CPU to the idlest affinity-compatible CPU.
- `set_priority` and `set_schedule_config` remove/reinsert ready tasks so queue placement stays consistent.
- `sys_schedctl` queries policy, updates non-deadline policy metadata, queries isolation fields, applies monotonic isolation restrictions, and admits deadline policy through op 4.
- Direct deadline activation through policy metadata returns `-95`; deadline admission returns `-22` for invalid budget tuples and `-28` for CPU bandwidth overload.
- Isolation restrictions can only tighten network, memory-page, thread, and capability-generation metadata.

## Compiler Checks

- `parse_task_attr` extends existing `@task` parsing.
- `validate_task_policy_attr` enforces runtime-family/effect constraints for RT/deadline policies.
