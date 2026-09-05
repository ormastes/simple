<!-- codex-design -->
# Parent-Commit Parallel Applications: Detail Design

## Data and control contracts

`TransferEnvelopeV1`, `StorageLayoutPlanV1`, and the parallel-commit result/receipt types are versioned common contracts. Transfer decisions are structural and include origin (`ParentOwned`, `ChildFresh`, `SharedImmutable`, `SharedSynchronized`, or external resource), boundary, source invalidation, and codec/lease requirement.

The runtime's smaller scalar-only actor record is named
`InlineValueEnvelopeV1`; it is an adapter for inline `RuntimeValue` words, not a
second definition of `TransferEnvelopeV1`. Scalar channel symbols are C-owned
under `rt_channel_*`; Rust object channels use `rt_value_channel_*`. Both are
finite and expose nonblocking backpressure. Process/remote object handles remain
non-admitting until an owner-scoped capability registry validates generation,
token, owner context, and revocation.

Task group sequence:

1. Parent freezes or references input revision.
2. Child receives copy/frozen/handle/owned input and allocates work in a task-local arena.
3. Child seals only disconnected output and sends it through a bounded typed envelope.
4. Parent validates type, ownership, revision, and declared access set.
5. Parent orders by the declared deterministic key, resolves conflicts, applies into a fresh commit arena, verifies, publishes, and emits a receipt.

Failure drops uncommitted child-local output and revokes leases; no consumed parent binding reappears. Unknown `Any`, unclassified pointer arithmetic, and process-local resources reject in safe transport. Dynamic indices are overlapping unless proven disjoint by range/partition facts.

For the scalar-text actor compatibility surface, `ActorScheduler` owns registry,
mailbox admission, ready publication, reply reservations, and terminal removal.
`ActorRef` is only the copyable `(actor_id, scheduler authority)` capability; it
cannot address a mailbox independently. Send and ask copy text-array arguments
into `ActorMessage` value storage. Full, closed, or unknown admission fails
before readiness is published. Stop removes the actor, cancels abandoned ask
reservations, closes the mailbox, and returns true only for the first terminal
transition observed by any copied reference. This compatibility payload is
narrower than a typed `TransferEnvelopeV1` actor endpoint and never authorizes
unchecked heap values.
The scheduler records its creator OS-thread identity. Registry, admission,
reply, lifecycle, query, and dispatch entrypoints compare the caller identity
and fail closed outside that domain. A copied reference is therefore a routing
capability, not permission for concurrent mutation; cross-thread actor sends
must use a future synchronized scheduler command ingress.

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

## Concrete structured owner/task API (2026-08-12)

The first executable API is split by ownership responsibility:

- `StructuredOwnerV1.snapshot()` returns copied values, revision, owner ID,
  deterministic digest, and an opaque scalar frozen-input token.
- `StructuredTaskGroupV1.reserve/publish_wire_result/fail_task/cancel_task/wait_all`
  owns bounded leases and terminal state independent of a runtime. The wire is
  eleven self-contained `i64` words with explicit success/failure and error
  code fields.
- `StructuredOwnerV1.commit()` calls the common commit validator, orders by the
  declared policy, applies to a cloned staging array, and publishes exactly
  once by advancing the owner revision.
- `RuntimeStructuredTaskGroupV1.spawn/map/join_all/wait_all` adapts the protocol
  to multicore-green handles. Each child has one private bounded scalar result
  channel and constructs `StructuredTaskWireResultV1`; the owner accepts it
  only if its task, sequence, region, kind, key token, revision, and live lease
  all match, then reconstructs `ResultEnvelopeV1` locally.
- `ActorStructuredTaskGroupV1.accept_result_message` decodes the same wire from
  a canonical bounded actor mailbox message and uses the identical lease gate.

`map` preflights count, regions, key, and remaining capacity before the first
reservation, so capacity+1 rejection is atomic. Cancellation revokes leases
and discards late messages while `join_all` still drains the worker. Allocation
failure rejects before reservation; joined channels are closed and freed so
the fixed native registry can reuse slots. The worker API accepts no function
or closure at all: `StructuredScalarWorker` selects only reviewed scalar
operations over the frozen token and copied scalar input.

`WorkerReportedFailure` is an explicit cooperative child result and produces a
`StructuredTaskFailureV1`. It is not a trapped runtime exit. The current pool
directly invokes closures and cannot convert an abort/panic into a result; docs
and receipts therefore make no trap-handling claim.
