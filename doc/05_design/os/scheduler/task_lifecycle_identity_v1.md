# Canonical task lifecycle identity V1

## Scope and owner

The scheduler identity allocator is the sole mutable owner of task lifecycle
identities. Each published `TaskControlBlock` contains one opaque
`{task_id, lifecycle_generation}` pair. Callers receive a copied pair; they do
not receive allocator state or permission to synthesize an identity.

## Allocation and publication

One checked mutex serializes both monotonic counters. Allocation validates both
counters before changing either, advances both under the same lock, and returns
the pair only after a successful unlock. Lock or unlock ambiguity quarantines
the allocator. A pair consumed before an unlock failure is burned and can never
be published or reused. Zero is reserved as invalid, task IDs stop before the
existing bounded PID ceiling, and neither counter wraps.

Every TCB construction path takes a fresh pair before publication: kernel task,
loaded user task, staged-byte user task, bootstrap user task, authenticated
loader adoption, ARM bootstrap handoff, and fork. Fork copies process state but
never copies the parent's lifecycle generation. Failure to allocate leaves the
TCB slot unpublished.

Exec replaces image-scoped state in the existing task and therefore preserves
the pair. It still revokes image-scoped launch authority and rotates address
space/capability state. Exit and reap never make a pair reusable.

## Current-task authority

`Scheduler.current_task_lifecycle_identity_v1()` resolves `Scheduler.current`
against the canonical TCB table and returns no identity for PID zero, a missing
TCB, or any zero component. `task_lifecycle_identity_v1(id)` provides the same
checked lookup for an explicit scheduler-owned `TaskId`. Filesystem and DBFS
owners consume these copied handles rather than accepting caller-supplied IDs.

## Complexity and layout

Allocation is O(1), performs no dynamic collection copies, and holds one mutex
for two scalar checks and increments. Current-task lookup is O(MAX_TASKS), which
matches the scheduler's existing bounded TCB lookup. The generation field
remains appended to the `@repr("C")` TCB, preserving prior field offsets.

## Static acceptance coverage

Focused scheduler specs assert nonzero distinct generations, fork separation,
and preservation across exec. Runtime execution is intentionally deferred by
the current no-verification instruction.
