# SimpleOS scheduler task-table transaction owner blocker

Status: implementation blocked at the canonical ownership boundary. No
transaction-owner source was retained, because a lifecycle-only wrapper would
leave existing unowned writers and would make the claimed serialization false.

## Required invariant

Each live `Scheduler` (including the filesystem-exec bootstrap scheduler) must
contain exactly one `SchedulerTaskTableOwnerV1` that owns its complete
fixed-capacity task table. This does not claim one process-global scheduler;
it requires that no live table has zero or multiple mutation owners.
Every create, fork, exec, block, wake, exit, kill, reap, priority-inheritance,
migration, dispatch, probe, and mapping-adoption mutation must execute through
that owner. A caller may receive a frozen snapshot, task identity, or terminal
receipt; it may not retain a mutable `[TaskControlBlock?]` alias.

The owner must use non-blocking/bounded acquisition in interrupt context,
compare the task's nonzero lifecycle generation before mutation, and issue a
bounded receipt containing operation, task identity, owner revision before and
after, and one of `Committed`, `Rejected`, or `Indeterminate`. If publication
commits but mutex release fails, the receipt and affected slot become
quarantined, the owner becomes poisoned, and later mutations fail closed.
Generation and revision exhaustion must retire the affected coordinate rather
than wrap.

## Why the current boundary cannot satisfy it

`Scheduler.tasks` is a directly mutable field on `Scheduler`. The lifecycle
surface is only one of several writer families:

- `_Scheduler/scheduler_lifecycle.spl` assigns the whole table for four create
  paths, exit, block, wake, and sleeper wake, and directly writes slots during
  yield, dispatch, tick accounting, naming, affinity, and policy changes.
- `_Scheduler/scheduler_priority_exec.spl` directly writes slots for priority
  inheritance, migration, wake placement, realtime/deadline accounting, fork,
  exec, and wait/reap.
- `_Scheduler/scheduler_green_lifecycle.spl` directly writes migration state.
- `scheduler_arm_bootstrap.spl` publishes a bootstrap TCB directly, and
  `scheduler_executable_adoption.spl` publishes an adopted executable TCB
  directly; neither passes through the lifecycle helpers.
- `scheduler_task_mgmt.spl` and `scheduler_exec.spl` accept and return mutable
  task arrays. Several helpers perform external side effects (FD close,
  namespace revocation, capability initialization, address-space destruction)
  before their caller publishes the returned array.
- `fs_exec_spawn.spl` constructs `Scheduler` directly, so adding owner state
  only in the normal constructor would create an unowned production path.

Locking only `create_task`, `block_task`, `unblock_task`, `exit_task_by_id`, and
`wait_for_collect` would therefore leave concurrent direct writers. Computing
`new_tasks` before acquiring a lock would also permit lost updates. Holding a
blocking mutex across interrupt-driven scheduling can deadlock when the
interrupted context owns it. Finally, an unlock-after-publication failure cannot
be represented safely while callers still own and assign the table themselves.

## Safe migration sequence

1. Add package-private `SchedulerTaskTableOwnerV1` whose private fixed table,
   bounded receipt ring, revision, poison flag, and mutex are created during
   serialized boot. Export a one-attempt interrupt ingress and a bounded
   thread-context ingress; do not expose the mutex handle.
2. Replace `Scheduler.tasks` with that owner. Move `_find_slot_in`, empty-slot
   selection, generation comparison, and table publication into it. Algorithms
   receive frozen snapshots or bounded query results, never the backing array.
3. Convert pure state changes first: yield, block, wake, priority, affinity,
   dispatch, and accounting. Every mutation ingress accepts an exact
   `{task_id, lifecycle_generation}` supplied by an already-authorized caller;
   a bare `TaskId` or a fresh current-table lookup is not sufficient mutation
   authority. Each transition returns a receipt plus generation- and
   owner-revision-bound side-state intents for deterministic application.
4. Convert create/fork/exec to prepare/commit. Resource allocation and image
   mapping produce an owned candidate; the task-table owner validates and
   commits it. Rejection returns the candidate to its resource owner for
   rollback. Exec must retain the old image, address space, mapping handles,
   grants, and cleanup authority until the replacement table commit succeeds.
   Only after task quiescence and terminal cleanup evidence may it retire the
   old resources; failure after replacement publication is indeterminate and
   quarantines the task rather than pretending the old image can be restored.
5. Convert exit/kill/reap to staged cleanup. Publish `Zombie` first, perform FD,
   namespace, mapping, and address-space cleanup through their existing owners,
   then commit terminal cleanup evidence before clearing the slot. An
   indeterminate cleanup remains a bounded quarantine tombstone.
6. Move bootstrap publication and executable adoption through the same owner;
   they may not receive a privileged direct-table escape hatch.
7. Update both `sched_new_with_topology_impl` and
   `_fs_exec_new_bootstrap_scheduler`, then remove all whole-table and direct
   slot assignments outside the owner in the same coherent change.

## Static acceptance gate for resumption

- `Scheduler` no longer exposes a `tasks` field. No direct backing-table read,
  write, whole-table assignment, receiver variant such as
  `scheduler.tasks[...]`, or mutable task-array alias/helper parameter remains
  outside `scheduler_task_table_owner_v1.spl`; all readers use frozen snapshots
  or bounded owner queries.
- Every mutation receipt binds the exact lifecycle generation and owner
  revisions; stale identities and replayed receipts reject.
- Interrupt callers never use the blocking lock path.
- Commit-before-unlock failure produces an `Indeterminate` receipt and sticky
  poison/quarantine; it is never reported as an ordinary rejection.
- Enqueue, dequeue, ready-queue, CPU-runqueue, `current`, `current_by_cpu`,
  preemption, deadline, realtime, and per-slot accounting changes are explicit
  generation/revision-bound side-state intents. Their terminal apply evidence
  is retained with the table receipt. Rejection applies none; failure after a
  table commit is indeterminate and poisons/quarantines the affected state.
- Reap cannot clear a slot until all required cleanup owners have returned
  terminal evidence.

This record is based on static source inspection only. No tests, builds,
SPipe, benchmarks, optimizer, bootstrap, or runtime verification were run.
