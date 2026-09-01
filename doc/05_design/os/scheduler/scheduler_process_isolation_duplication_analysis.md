# Scheduler Process Isolation Duplication Analysis

Date: 2026-05-17

## Scope

This analysis covers the scheduler/process-isolation work currently staged around:

- `src/os/kernel/scheduler/process_isolation.spl`
- `src/os/kernel/scheduler/sched_class_queue.spl`
- `src/os/kernel/scheduler/sched_policy_engine.spl`
- `src/os/kernel/ipc/syscall_scheduler.spl`
- `test/01_unit/os/scheduler_isolation_spec.spl`

It compares the new modules against existing scheduler, syscall, realtime, and scheduler-service code.

## Result

The work is not an exact duplicate by symbol name, but it does overlap existing scheduler responsibilities.

No exact public symbol collisions were found for the main new concepts:

- `ProcessIsolationPolicy`
- `ProcessIsolationManager`
- `SchedulerPolicyEngine`
- `SchedClassQueue`
- `SyscallScheduler` / scheduler syscall handler helpers

The new files also compile cleanly with `bin/simple check`.

## Existing Areas With Related Responsibility

The following existing modules already own adjacent scheduler behavior:

- `src/os/kernel/scheduler/scheduler_types.spl`
  - Core scheduler task state, topology, default schedule/isolation setup, and scheduler-global state.
- `src/os/kernel/scheduler/scheduler_algorithm.spl`
  - Existing scheduling algorithm responsibility.
- `src/os/kernel/scheduler/scheduler_task_mgmt.spl`
  - Existing task lifecycle and scheduler mutation responsibility.
- `src/os/kernel/ipc/syscall_*.spl`
  - Existing syscall handler structure and dispatch pattern.
- `src/os/kernel/ipc/syscall_security_debug.spl`
  - Already calls scheduler isolation restriction paths for pledge/unveil/capability operations.
- `src/os/realtime/scheduler.spl`
  - Separate realtime scheduler implementation with priority, bitmap, current task, and tick behavior.
- `src/os/services/sched_service.spl`
  - User-space scheduler policy service with class constants, priority recommendation, tick accounting, and priority feedback.

## Overlap Assessment

### Process Isolation

`process_isolation.spl` introduces a standalone isolation model with capability grant/deny text fields and escalation rules.

This is not a direct duplicate of an existing symbol, but it overlaps with existing kernel scheduler isolation state and with `syscall_security_debug.spl`, which already restricts current-task isolation for security syscalls.

Refactor direction:

- Treat `process_isolation.spl` as the reusable policy/evaluation layer.
- Keep actual task ownership and mutation in the existing scheduler task-management layer.
- Route pledge/unveil/capability syscalls through the shared isolation evaluator instead of growing parallel policy code.

### Class Queues

`sched_class_queue.spl` introduces per-class and per-CPU queue behavior.

This is not an exact duplicate, but it overlaps with the existing scheduler algorithm and realtime scheduler priority queues.

Refactor direction:

- Keep queue ordering and starvation helpers here only if they are used as a narrow data-structure module.
- Move scheduler decisions that need global task/topology state into `scheduler_algorithm.spl`.
- Avoid adding a second scheduler state owner.

### Policy Engine

`sched_policy_engine.spl` coordinates class validation, preemption, starvation prevention, time slicing, and affinity routing.

This overlaps most strongly with `scheduler_algorithm.spl`, `scheduler_task_mgmt.spl`, and `sched_service.spl`.

Refactor direction:

- Keep pure policy calculations in `sched_policy_engine.spl`.
- Keep kernel task mutation in `scheduler_task_mgmt.spl`.
- Keep user-space adaptive policy in `sched_service.spl`.
- Do not duplicate class constants between kernel and service; introduce a shared class mapping if both layers need the same values.

### Scheduler Syscalls

`syscall_scheduler.spl` introduces schedule/schedctl request handling and decoding helpers.

This fits the existing syscall split pattern, but must integrate with the main syscall dispatcher instead of becoming a parallel path.

Refactor direction:

- Keep request decoding helpers local to `syscall_scheduler.spl`.
- Delegate state mutation to existing scheduler APIs.
- Register handlers through the same mechanism as other `syscall_*.spl` modules.

## Test Gap

`test/01_unit/os/scheduler_isolation_spec.spl` currently compiles and runs through the test runner, but the runner reported `0` examples in the previous check. That means the file is useful as an executable/manual validation harness, but it is not yet strong automated test evidence.

Required follow-up:

- Convert manual `test_*` functions into runner-discovered examples or the repository's expected spec form.
- Keep coverage focused on:
  - class validation
  - priority bounds
  - preemption ordering
  - starvation boost behavior
  - CPU affinity routing
  - isolation escalation rejection
  - syscall schedule/schedctl decoding

## Decision

Keep the new modules, but treat them as a refactor-in-progress:

- Not exact duplicate: acceptable to commit as isolated modules.
- Has responsibility overlap: must be integrated before declaring the scheduler architecture complete.
- Highest-risk issue: ineffective automated tests.
- Next refactor target: connect policy/syscall modules to existing scheduler state and replace manual spec functions with real discovered examples.
