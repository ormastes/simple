# V4 start can lose the child lease after native launch

Status: open. Priority: P1. Owner: process observation V4 runtime and Simple owner facade.

`process_observation_owner_start_pinned_v4` in
`src/lib/nogc_sync_mut/io/process_ops.spl` calls the native pinned start,
then decodes its returned wire with `?` and validates ticket fields. Either
step may return `Err` without an owned `ProcessObservationLeaseV4`. The native
start in `src/runtime/runtime_process_owned.c` can already have launched and
retained a child before producing that wire. Its
`pov4_abandon_unpublished` cleanup handles native tuple publication failure,
but it cannot observe a later Simple-side decode or ticket-validation error.

This blocks a production distributed-build transport supervisor from treating
all start errors as `no child`. Until repaired, an error after the native call
requires reconciliation and retention of the prepared upload and handoff
roots; it does not authorize child-byte verification or cleanup of those roots.

Repair the owner boundary so every post-launch outcome returns either a live
lease with a bounded cancel/collect/ack path or native proof that the child and
all qualified descendants have stopped. Add fault-injected malformed start
receipt and ticket cases after successful launch, with exact no-orphan and
resource-cleanup evidence. Run the source-matched Simple and native V4 specs
before enabling distributed parallel dispatch.

The native start currently allocates a four-part return tuple before launch,
then replaces its words after launch. It calls `pov4_abandon_unpublished` only
when native tuple publication fails. A safe repair needs a recovery authority
that is independent of the decoded receipt fields: return a separately bound
opaque lease or make native start retain and reconcile every unacknowledged
publication failure. The Simple facade must not infer `no child` from a
decode error. Qualify the recovery path when the receipt payload or ticket
words are malformed after a successful native launch, including concurrent
starts, timeout, and cleanup failure.
