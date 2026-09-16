# Parallel runtime: raw RuntimeValue transport violates isolation

- **Date:** 2026-08-12
- **Severity:** P0 (ownership/isolation correctness)
- **Owner:** WP-13/WP-16/WP-17 runtime transport lanes

## Observed

`src/compiler_rust/runtime/src/value/core.rs:484` documents `deep_copy()` as a
placeholder and returns the original heap value for non-channel heap objects.
`src/compiler_rust/runtime/src/value/actors.rs:98-144` serializes actor message
and reply `RuntimeValue` raw bits, then reconstructs them with `from_raw`.
`src/compiler_rust/runtime/src/value/channels.rs:65-104` uses an unbounded
`mpsc::channel<RuntimeValue>` and sends the value without transfer-class
validation.

Heap-backed values therefore retain process-local pointer identity through
paths documented as isolated/copied. This contradicts safe cross-domain
ownership and invalidates optimizer alias assumptions.

## Expected

Safe actor, thread, and process transport must classify input and use a typed
transfer envelope. Process/remote paths must use codec/object-handle/immutable
payloads; no raw RuntimeValue heap bits may cross. Default mailboxes must have
a finite capacity and report closure/backpressure failures.

## Unblock condition

Implement the common `TransferEnvelopeV1` contract in the runtime, replace
raw-bit actor transport and unbounded channel payload transport, implement
graph clone/freeze/seal semantics, and add real heap graph, separate-process,
closed-channel, bounded-backpressure, and cancellation rollback tests. Verify
through an admitted self-hosted binary and native runtime evidence.

## 2026-08-12 partial mitigation

The native runtime now fails closed for the unsafe compatibility paths:

- `RuntimeValue::deep_copy()` returns `NIL` for mutable heap graphs instead of
  preserving their pointer identity; explicit channel handles remain shared.
- native channel send rejects every heap-tagged payload until a typed envelope
  decoder owns that payload class;
- actor send and reply encode inline values only and reject heap addresses.

Focused native tests pass for actor rejection, channel rejection, and mutable
heap-copy rejection. This does **not** close the P0: bounded mailboxes, typed
graph/envelope transport, ownership-token lifecycle, actor/process codecs, and
real cancellation/backpressure evidence remain required.

## 2026-08-12 typed-packet progress

The native value runtime now implements the frozen 40-byte `SPTR` v1 metadata
contract and a fixed-size 48-byte inline packet. The native actor path encodes
and decodes that packet without a per-message byte-vector allocation instead of
reconstructing an eight-byte raw value, rejects heap
construction context, and the native compatibility channel stores typed packets
in a finite 256-item queue. A full queue returns send failure rather than
blocking while holding its compatibility mutex.

The Simple/native golden envelope agrees byte-for-byte. Native tests cover
reserved fields, unknown/heap value tags, packet round trip, actor context
rejection, finite capacity, and existing channel behavior. Test compilation
currently requires temporarily omitting the unrelated broken
`rt_io_tcp_probe_peer` re-export already present on `origin/main`; that omission
is not part of this change.

The P0 remains open for typed frozen/owned/encoded graph payloads,
policy-selected mailbox capacities, ownership-token lifecycle, close/free concurrency hardening,
separate-process transport, cancellation rollback, and admitted self-hosted
end-to-end evidence.

## 2026-08-12 encoded process-frame progress

The native runtime now has a bounded process frame over the same `SPTR` v1
metadata. Only `EncodedCopy` is admitted for the process destination; the frame
adds an exact payload length, stable corruption checksum, a 4 MiB ceiling, and
destination-domain validation. Region IDs combine the current process ID with
a bounded local sequence so independently executing parent/child allocators
cannot collide. A real child test process decodes a parent-created frame and
writes a child-created encoded result for the parent to validate. Wrong-target,
wrong-route, corrupt, and oversized frames fail closed.

The previously named `rt_pg_parallel_worker_handoff_*` ABI is absent from
current `main` and is not reintroduced: its aggregate pointer-retention model
would contradict this contract. Production `native_spawn_worker` and C piped
process APIs are not yet connected to the frame, so this is foundational
separate-process evidence rather than public process-transfer completion.

The P0 remains open for registered graph/schema codecs, ObjectRef transport,
production spawn/piped integration, ownership-token lifecycle, cancellation
rollback, close/free concurrency hardening, and admitted self-hosted evidence.

## 2026-08-14 parent-ingress progress and remaining actor boundary

The Simple runtime now connects one bounded `SPRF1` piped stdout reader to a
copied `SPRS` parent inbox. `ParentCommitPipedProcessSessionV1` owns one child
handle; the paired inbox rejects generation mismatch and repeated region IDs,
and explicit close is idempotent. This resolves the previously listed absence
of any spawn/piped result ingress, but it does not close the P0.

`ActorRef.send()` still admits directly through its mailbox and native
`rt_actor_send` discards full/closed failure. The scheduler is single-threaded,
so mailbox locking cannot establish safe copied-ref cross-thread admission.
Typed graph/ObjectRef transport, a checked scheduler-owned actor ingress,
policy-selected capacity, cancellation/terminal receipts, and admitted Stage 4
evidence remain required. Session freshness and replay lifecycle details are
tracked separately in
`process_transfer_session_replay_identity_2026-08-12.md`.
