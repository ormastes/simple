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

## Runtime Integration Status (2026-07-08)

The data structures and algorithms above are implemented (`src/os/kernel/scheduler/*.spl`,
4,850 lines total, verified `wc -l` 2026-07-08) but **none of it runs at
runtime today**. The x86_64 kernel image the QEMU spec boots is a probe
fixture that never enters ring-3; the one path that reaches CPL3,
`x86_64_fs_exec_enter_image_ring3` in
`src/os/kernel/loader/x86_64_fs_exec_ring3.spl:270`, iretq's directly and
exits QEMU on process exit (its own docstring says so, lines 273-274) —
it never calls back into this scheduler. Two more gaps compound this:

- No per-process kernel stack — `kernel_stack: 0` at every task-creation
  site (`scheduler_task_mgmt.spl:80`, `scheduler_exec.spl:212`, `:263`,
  `scheduler_arm_bootstrap.spl:127`); no kernel-stack allocator; nothing
  sets `TSS.RSP0`.
- No timer-tick wiring — the RISC-V64 hook is commented out
  (`# scheduler_tick()` at `arch/riscv64/timer.spl:166`), and the x86_64
  timer (`arch/x86_64/timer.spl`) has no scheduler hook at all.

So this design is implemented-but-unwired: dead at runtime until the
FS-exec keystone runs a real ring-3 process and returns to the scheduler
instead of exiting QEMU. See
`doc/03_plan/agent_tasks/simpleos_missing_os_subsystems_report.md` (the
capability audit) and
`doc/02_requirements/os/simpleos/simpleos_os_subsystem_feature_requests.md`
FR-SOS-036/038/039 (the M2 return-to-scheduler track) for the fix plan.
