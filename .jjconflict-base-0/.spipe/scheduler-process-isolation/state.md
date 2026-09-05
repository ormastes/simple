# SStack State: scheduler-process-isolation

## Status: CLOSED — 2026-05-20

## User Request
> next task from the plan — scheduler_process_isolation (5 tasks: data structures, per-CPU queues, syscalls, @task parser, verification)

## Task Type
feature

## Refined Goal
> Extend SimpleOS scheduler with per-CPU class queues, process isolation data structures, sys_schedule/sys_schedctl syscall handlers with C-ABI shims, @task parser extensions, and focused verification specs.

## Acceptance Criteria
- [x] AC-1: Extended task struct — priority class (realtime/normal/batch/idle), CPU affinity mask, time slice, isolation level, deadline fields
- [x] AC-2: Scheduler class queues — per-CPU ready queues partitioned by priority class, with enqueue/dequeue/rebalance
- [x] AC-3: Process isolation levels — none/namespace/container/sandbox with capability restrictions per level
- [x] AC-4: sys_schedule handler — schedule(pid, class, priority, affinity) syscall with validation
- [x] AC-5: sys_schedctl handler — schedctl(pid, op, value) for get/set priority, affinity, time slice, isolation level
- [x] AC-6: C-ABI shims — extern fn wrappers for sys_schedule and sys_schedctl matching kernel ABI convention
- [x] AC-7: @task parser extension — @task annotation with class/priority/affinity/deadline fields parsed from source
- [x] AC-8: Task validation — validate @task annotations (range checks, class enum, affinity mask format)
- [x] AC-9: Scheduler policy engine — time slice calculation, preemption decisions, starvation prevention
- [x] AC-10: Verification spec — 20 tests covering task creation, queue operations, syscalls, isolation, policy

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-17
- [x] 2-4 — skipped (plan doc comprehensive)
- [x] 5-implement (Engineer) — 2026-05-17
- [x] 6-refactor (Tech Lead) — 2026-05-17
- [x] 7-verify (QA) — 2026-05-17
- [x] 8-ship (Release Mgr) — 2026-05-17

### 6-refactor
Duplication analysis added at `doc/05_design/scheduler_process_isolation_duplication_analysis.md`.
Result: no exact public symbol duplication; responsibility overlap remains with scheduler task management, scheduler algorithm, syscall dispatch, realtime scheduler, and scheduler service modules.

### 7-verify
20/20 tests PASS. Commit b25c3b8a91 pushed to origin/main.

## Phase Outputs

### 1-dev
10 ACs across 5 plan items. 5 parallel agents (A-E). Existing: scheduler (13 files), task_types.spl, scheduler_task_mgmt.spl, syscall_process.spl, capability.spl.

### 5-implement
5 parallel Sonnet agents. 5 files created:
- src/os/kernel/scheduler/sched_class_queue.spl — SchedClass + SchedTask + ClassQueue + PerCpuScheduler + MultiCpuScheduler
- src/os/kernel/scheduler/process_isolation.spl — IsolationLevel + ProcessIsolationPolicy + IsolationEnforcer + NamespaceMapping + NamespaceRegistry
- src/os/kernel/ipc/syscall_scheduler.spl — SchedRequest + SchedctlOp + SysScheduleHandler + SysSchedctlHandler + SchedSyscallShim
- src/os/kernel/scheduler/sched_policy_engine.spl — TaskAnnotation + TaskAnnotationValidator + TimeSliceCalculator + StarvationPrevention + SchedulerPolicyEngine
- test/01_unit/os/scheduler_isolation_spec.spl — 20 tests
