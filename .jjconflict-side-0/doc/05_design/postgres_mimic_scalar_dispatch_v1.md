# PostgreSQL Mimic Scalar Dispatch V1

The parent owns `PgDispatchGate`, `PgDatabaseOwner`, the dispatch-port queue,
and all lifecycle mutation. Workers own sockets and parsers. Their only shared
identity is a copied dispatch-port token.

The first implementation slice must prove submit and completion end to end:
worker publishes a fully copied request, parent drains and calls `submit`, then
publishes the scalar job id; after owner completion, the parent publishes a
fixed completion result which the worker consumes. Startup, take, cancel, and
complete request opcodes remain reserved and return `UNSUPPORTED` until their
owner adapters exist.

Required tests cover capacity plus one, wrong family, stale generation, text
length/hash/copy immutability, unsupported opcode rejection, submit result
visibility only after parent drain, completion consumption, shutdown rejection,
and release only after worker join. The Simple source contract must reject any
`PgDispatchGate`, config aggregate, raw pointer, or non-scalar thread argument
in the worker descriptor path.

## Current integration boundary

`PgScalarParallelOwnerV1.pump_one` now provides the parent-side transition:
it claims one scalar port record, reconstructs bounded copied text on the
database-owner thread, submits it to that owner's canonical `PgDispatchGate`,
runs one owner command, takes the completion, encodes canonical pgwire bytes,
and publishes a scalar blob receipt. Every rejected, malformed, timed-out, or
encoding-failed branch aborts the claim exactly once. This proves the owner
side without making a worker-side `PgWireFrontendDispatcher` safe.

The live `PgWireParallelLinuxServer` remains HOLD. Its current frontend still
stores a `PgDispatchGate`, and its compatibility descriptor still uses
aggregate dispatch/config reconstruction. The next admission work is a
scalar-port frontend that owns only a transport driver, scalar request ids,
and bounded local protocol state; only then may the server switch its worker
entrypoint to this port.
