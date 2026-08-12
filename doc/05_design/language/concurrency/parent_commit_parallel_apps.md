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

Required future SSpec flow helpers are `step_create_parent_snapshot`, `step_send_child_result`, `step_commit_results_in_order`, and `check_no_raw_pointer_transport`. Unwired scaffolds fail with `fail("parallel ownership contract not wired")`.
