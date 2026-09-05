# PostgreSQL Mimic Worker Scalar ABI

The server parent owns control, dispatch, limits, configuration, listener
lifecycle, descriptors, and join handles. A worker entry receives only a
generation-tagged descriptor token and a scalar reserved argument. Descriptor
storage in `runtime_db.c` is bounded to 1024 immutable six-word entries and
uses a family tag so wrong-kind tokens reject. Release increments generation;
the parent performs it only after the corresponding thread joins.

Limits use the owner-checked scalar limits registry and are reconstructed from
eight copied `i64` fields in the worker. The former aggregate worker handoff and
lambda callback are removed. Dispatch and text configuration still use their
typed owner registries because their operation codecs are not yet scalarized;
therefore this lane does not yet claim the full requested aggregate-free worker
ABI. Those registries must be replaced by dispatch operation/result cursors and
immutable text-identity handles before production admission.

The focused source gate links `runtime_db.c` with the canonical minimal runtime
owner, `runtime_native.c`, using section garbage collection so unrelated runtime
subsystems do not become descriptor-test dependencies. The immutable capsule
also registers the same descriptor receipt and asserts that all three exported
descriptor functions have exactly one provider, `runtime_db.o`.

Control and result cursors now occupy distinct scalar handle families, so a
result cursor cannot be used as a control and a control cannot be read through
result getters. Limits creation is registered with its exact nine-argument
SFFI shape. If worker reconstruction fails, the named worker entry reads the
descriptor-owned listener fd and closes it before returning; after every
started worker joins, the parent releases each descriptor and its referenced
views exactly once. Parallel server admission remains HOLD for the unsolved
dispatch/config aggregate registries.

## Frozen dispatch transport V1

The replacement boundary is an owner-created `PgDispatchPortV1`, never a
`PgDispatchGate` value.  Its generation-tagged family token names a bounded
MPSC request queue and a bounded result table.  A worker descriptor contains
only that token.  The database-owner thread is the sole consumer and the sole
caller of `PgDispatchGate`; workers can only publish or read fixed scalar
records.

Request words are `(version, operation, request_id, connection_id, session_id,
argument0, text0, text1, text2, deadline_ms)`.  Result words are `(version,
request_id, status, value0, value1, text0)`.  `operation` is frozen as:
`1=submit`, `2=startup`, `3=take`, `4=cancel`, `5=complete`.  Unknown versions,
operations, full queues, stale tokens, and wrong-family text/result handles are
rejected without publication.  V1 may enable operations incrementally, but a
disabled operation returns `UNSUPPORTED`; it never falls through to another
operation.

Text fields are immutable registry entries copied at publication, bounded to
256 bytes each, and store length plus a 64-bit content hash.  Their family and
generation are validated on every access.  The worker releases request-owned
text only after publication fails or after its result is consumed; the owner
releases text for rejected/drained requests.  No raw pointer or Simple text
RuntimeValue is retained.

The owner drain algorithm dequeues at most a caller-provided budget, validates
the complete record, reconstructs copied text locally, applies exactly one
`PgDispatchGate` transition, and publishes a result keyed by request id.  A
result becomes visible only after the lifecycle transition completes.  Queue
drain, result publication, and release are generation checked.  Shutdown first
rejects new publications, drains or rejects queued records, joins every worker,
then releases the port and config handles.

Server admission remains HOLD until submit and completion are both exercised
through this transport and `PgWireFrontendDispatcher` no longer stores or calls
a worker-side `PgDispatchGate`.  Merely placing an aggregate RuntimeValue behind
an integer token does not satisfy this contract.

As of the current slice, `PgScalarParallelOwnerV1.pump_one` is the canonical
parent adapter: scalar claim -> parent-owned `PgDispatchGate` ->
`PgDatabaseOwner.process_bounded` -> canonical encoded blob -> scalar result.
It consumes/aborts every claim and never passes a gate or config aggregate
through an extern boundary. This is parent-only evidence, not live worker
admission. The worker must still be migrated from `PgWireFrontendDispatcher`
to an equivalent scalar-port frontend before the descriptor's dispatch field
can safely carry a port token.

The current unwired prototype implements the Submit/Complete transport in C.
Completion returns a distinct family-tagged result receipt; reading status or
value is side-effect free and one explicit release atomically consumes it.
Owner payload access rechecks the copied bytes against their stored length/hash.
Capacity, wrong-family, stale-port, and stale-result behavior are covered by the
focused prototype gate. It is registered in native SFFI and runtime symbol
retention, but is not server evidence; the server remains HOLD.

Completion payloads use a separate family-tagged immutable byte registry: 64
concurrent blobs, each bounded to 64 KiB. Creation copies canonical encoded
bytes plus scalar session/close fields and records a content hash; worker reads
metadata and individually hash-validated bytes, then explicitly releases the
generation receipt. Cancel and terminate are distinct queue opcodes. This is
still unwired until the Simple owner adapter provides canonical pgwire bytes.

Owner consumption now uses family-tagged claim receipts. Claim atomically
copies and dequeues one request into a bounded 64-entry inflight table; parent
jobs may then complete in any order. Completion publishes the request-keyed
result before consuming the claim exactly once. Per-text length/hash metadata
and byte cursors are available both at the queue head and through the claim.
