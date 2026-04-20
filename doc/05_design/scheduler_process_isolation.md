<!-- codex-design -->
# Detail Design: Scheduler + Process Isolation

## Data Structures

- `SchedulerPolicy`: `Internal`, `Fair`, `Background`, `RtFifo`, `RtRoundRobin`, `Deadline`, `Idle`.
- `TaskScheduleConfig`: policy metadata, fair accounting, deadline budget fields, affinity and home CPU.
- `TaskIsolationProfile`: address-space id, capability generation, sandbox defaults, resource caps.
- `CpuRunQueue`: per-class ready queues and local load counters.

## Algorithms

- Enqueue mirrors legacy priority queues and per-CPU class queues.
- Schedule picks from CPU 0 in v1 and uses class order. Fair/background lanes pick the eligible task with the earliest virtual deadline.
- `set_priority` and `set_schedule_config` remove/reinsert ready tasks so queue placement stays consistent.
- `sys_schedctl` queries policy and updates policy metadata; deadline activation returns `-95`.

## Compiler Checks

- `parse_task_attr` extends existing `@task` parsing.
- `validate_task_policy_attr` enforces runtime-family/effect constraints for RT/deadline policies.
