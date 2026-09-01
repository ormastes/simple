# PostgreSQL Mimic B2 Concurrency Gate (2026-08-11)

Status: **OPEN — hosted adapter is serial and is not benchmark-admissible.**

## Finding

`PgWireLinuxServer.serve_once` accepts a socket and calls `serve_connection`
synchronously.  `serve_bounded` cannot return to `accept` until that client
closes.  Consequently, one idle keepalive client can prevent every later client
from being accepted.  `active_sessions` cannot exceed one in this implementation.

Adding `task_spawn` around `serve_connection` is unsafe: the closure would share
mutable `PgWireLinuxServer`, `PgDatabaseOwner`, and `PostgresMimicServer` state
without a proven thread-safe ownership boundary.

## Selected B2 design

1. A fixed-size async socket-worker set owns connections and protocol parsers.
2. Workers never access `PostgresMimicServer` directly.  They submit bounded,
   typed jobs carrying connection, session, operation, and deadline identity.
3. One database-owner executor performs session/transaction mutations and sends
   typed completions to the originating worker.  Queue-full and deadline expiry
   fail closed with PostgreSQL-compatible overload/error responses.
4. Read scaling or database sharding is a later evidence-gated optimization;
   it must preserve transaction affinity and durability-before-ACK.
5. Drain stops admission, cancels queued work, completes active work within a
   bound, checkpoints, and only then closes the database.

## Admission evidence

- Two concurrent clients must both complete while the first keeps its socket open.
- A stalled client must not prevent new accepts or database-owner progress.
- Queue saturation, disconnect, timeout, and drain must reclaim every job once.
- Transaction isolation and durability specs must remain green.
- Only after live pgwire interoperability may pgbench compare this server with
  PostgreSQL using identical schema, data, durability, clients, and duration.

Until these checks pass, reports must call this surface a bounded serial hosted
adapter, not a concurrent or PostgreSQL-performance-equivalent server.
