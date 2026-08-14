<!-- codex-design -->
# Parent-Commit Parallel Applications: Detail Design

## Data and control contracts

`TransferEnvelopeV1`, `StorageLayoutPlanV1`, and the parallel-commit result/receipt types are versioned common contracts. Transfer decisions are structural and include origin (`ParentOwned`, `ChildFresh`, `SharedImmutable`, `SharedSynchronized`, or external resource), boundary, source invalidation, and codec/lease requirement.

Task group sequence:

1. Parent freezes or references input revision.
2. Child receives copy/frozen/handle/owned input and allocates work in a task-local arena.
3. Child seals only disconnected output and sends it through a bounded typed envelope.
4. Parent validates type, ownership, revision, and declared access set.
5. Parent orders by the declared deterministic key, resolves conflicts, applies into a fresh commit arena, verifies, publishes, and emits a receipt.

Failure drops uncommitted child-local output and revokes leases; no consumed parent binding reappears. Unknown `Any`, unclassified pointer arithmetic, and process-local resources reject in safe transport. Dynamic indices are overlapping unless proven disjoint by range/partition facts.

## Layout policy

The planner resolves ABI constraints first, then assurance/profile overrides, declaration attributes, project/target policy, cost-model/PGO suggestions, and conservative fallback. Layout plan and source revision key cached views. AoS is the reference; SoA/AoSoA/grouped views lower logical field projections without exposing contiguous element assumptions.

## Initial system-test matrix

| Requirement | Scenario |
|---|---|
| REQ-PAR-003/004 | explicit parent move consumes source; child-fresh output returns once |
| REQ-PAR-005/006 | typed bounded transport rejects pointer/unknown dynamic input and exposes backpressure |
| REQ-PAR-007 | disjoint scoped loans join; overlap/escape rejects |
| REQ-PAR-008/009 | randomized completion yields one ordered parent receipt; stale/conflict rejects atomically |
| REQ-MEM-001..003 | AoS/SoA parity, ABI rejection, stale-view rejection |

The actor/process completion SSpec freezes these operator-visible steps:

1. `Create a bounded parent-owned process session`.
2. `Receive a fragmented encoded child result`.
3. `Reject stale or replayed child output`.
4. `Commit one validated batch at the parent`.
5. `Close the child transport exactly once`.

The frozen setup/checker helpers are `child_result_line`,
`parent_commit_frame_inbox_v1_for_generation`,
`parent_commit_piped_process_session_v1`, and `drain_process_result_batch`.
Unwired scaffolds fail with `fail("parallel ownership contract not wired")`.

Actor admission is not yet a cross-thread contract. `ActorScheduler` is a
single-threaded owner, while current `ActorRef.send()` directly enqueues and
then touches the ready queue. The implementation phase must choose exactly one
of two falsifiable designs: constrain all reference operations to the scheduler
execution domain, or add one scheduler-owned synchronized command ingress.
Mailbox locking alone cannot justify concurrent copied-reference safety.
