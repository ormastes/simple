# SStack State: scheduler-process-isolation

## User Request
> next task from the plan — scheduler_process_isolation (5 tasks: data structures, per-CPU queues, syscalls, @task parser, verification)

## Task Type
feature

## Refined Goal
> Extend SimpleOS scheduler with per-CPU class queues, process isolation data structures, sys_schedule/sys_schedctl syscall handlers with C-ABI shims, @task parser extensions, and focused verification specs.

## Acceptance Criteria
- [ ] AC-1: Extended task struct — priority class (realtime/normal/batch/idle), CPU affinity mask, time slice, isolation level, deadline fields
- [ ] AC-2: Scheduler class queues — per-CPU ready queues partitioned by priority class, with enqueue/dequeue/rebalance
- [ ] AC-3: Process isolation levels — none/namespace/container/sandbox with capability restrictions per level
- [ ] AC-4: sys_schedule handler — schedule(pid, class, priority, affinity) syscall with validation
- [ ] AC-5: sys_schedctl handler — schedctl(pid, op, value) for get/set priority, affinity, time slice, isolation level
- [ ] AC-6: C-ABI shims — extern fn wrappers for sys_schedule and sys_schedctl matching kernel ABI convention
- [ ] AC-7: @task parser extension — @task annotation with class/priority/affinity/deadline fields parsed from source
- [ ] AC-8: Task validation — validate @task annotations (range checks, class enum, affinity mask format)
- [ ] AC-9: Scheduler policy engine — time slice calculation, preemption decisions, starvation prevention
- [ ] AC-10: Verification spec — 20 tests covering task creation, queue operations, syscalls, isolation, policy

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-17
- [x] 2-4 — skipped (plan doc comprehensive)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
10 ACs across 5 plan items. 5 parallel agents (A-E). Existing: scheduler (13 files), task_types.spl, scheduler_task_mgmt.spl, syscall_process.spl, capability.spl.

### 5-implement
<pending>
