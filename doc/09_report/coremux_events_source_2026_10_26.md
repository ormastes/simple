# Per-lease event journal — source candidate

Baseline `3006afa9b4dd286e3beb304dbe4f1a57cf5d87a8`. Source cycle 3.
**WARN / NOT_RUN: ten modern SSpec cases authored, zero executed.**
No compiler, test, native process, helper, watchdog or server launched.

## Interfaces and ownership

`CoreMuxEventJournalV1` holds one exact MuxHandleV1, last cursor, discarded-through
cursor, retained MuxEventV1 array and count/byte limits. It contains no session,
pane, child, native handle, output buffer or authentication controller.

- `core_mux_events_new_v1(handle,max_events,max_bytes)` validates empty retention.
- `core_mux_events_can_advance_v1(journal,handle,count)` checks all planned serials
  against u64 exhaustion before owner effects. Count zero permits an actual no-op.
- `core_mux_events_append_v1(journal,handle,causal_id,revision,kind)` assigns one
  cursor to an actual caller-supplied observation and returns the new value.
- `core_mux_events_poll_v1(journal,handle,after,limits)` returns the existing typed
  batch without consuming records, polling children, renewing or authenticating.

Exact handle matching includes owner ID, generation and lease token; shape checks
do not grant authority. The server must authenticate and check expiry/revocation
before invocation. Preflight is not a reservation: the single owner must serialize
the check, effects and publication and budget every event those effects can emit.
No event is proof that its supplied native observation actually happened.

## Retention and byte accounting

Retention permits 1..1024 events and 256..1048576 conservative encoded bytes,
including full batch overhead. An owner ID whose empty batch exceeds a chosen
budget is refused. Canonical `mux_wire_size_mux_event_batch_v1` computes overhead;
event contributions use the existing event-size function plus its two-byte
array separator allowance. Fixed conservative u64/bool charges make overhead
independent of cursor values. No external or cached byte charge is trusted.
Whole-batch sizing is rechecked for replies to detect codec accounting changes.

This bounds retained encoded representation, not caller-owned input allocations,
object allocator overhead or the outer transport envelope. Count bounds also
limit record overhead. Admission and polling validate internal contiguity and
canonical event shape; malformed observations return an error without mutation.
Bounded scans are linear in retained records apart from canonical nested value
validation. No full service scans, host access, parser duplication or unbounded
buffer concatenation is introduced.

Oldest count/byte eviction moves discarded_through. A valid event individually
larger than retention still consumes a serial, discards old retained records and
sets the loss floor to that serial. Polling from an older cursor explicitly sets
reconciliation_required; an empty loss batch advances to the loss floor. It is
not an invented event or silent success for an unobserved native operation.
Reading at/after the loss floor does not falsely report a new gap. Pagination
stops at the last returned event; insufficient budget for the next event refuses
rather than returning a stalled success or skipping it. Future cursors refuse.

## Integration and verification limits

The journal is not yet attached to API publication, content ingestion or native
notification observations. Server composition must allocate/manage per-lease
journals under its global budget, reserve serial capacity before effects, enforce
expiry, retain or dispose journals by explicit policy, and reconcile snapshots
after loss. A poll response does not acknowledge or extend the caller's lease.
Prequalification evidence remains NotRun and full mandatory admission is not
advertised by the presence of this helper.

The focused spec uses literal expected cursor results, production admission and
actual canonical SDN serialization for byte-bound comparisons. Near-MAX states
are explicitly pure boundary fixtures. No fake native event generator or
replacement test framework is used. Root controls Phase 2 functional execution
and records its actual legacy profile; current --library-mode behavior, full
native/system workflows, both providers and N2 remain independent requirements.

Before independent review, the initial freeze's appended-array alias assumption
was removed: append now copies retained elements into a fresh array before push.
The input journal cannot be modified even if configured array assignment shares
storage. V1 remains historical; v2 pins this narrow ownership correction. Existing
immutability assertions remain authored and unexecuted.

## Cycle 3 — checked array construction

Independent source review found that owned array allocation failure can leave
push/cardinality unchanged. Advancing a poll cursor after an unchecked push could
skip an event without reconciliation. Singleton cardinality is now checked before
validation; every copy/append checks length; slicing checks exact tail count;
the constructed journal is validated before return. Poll advances only after a
successful selected-array length increase and validates the final batch.
Construction failure returns Unavailable without mutating the original journal.

The invalid-state scenario now also rejects a missing retained tail and duplicate
cursor through production paths. These controls are not allocation injection;
native allocator exhaustion remains unexecuted. NotApplied on a helper error
describes journal mutation only: an integrating owner that already performed
native effects must retain/translate its actual Partial/Unknown receipt rather
than claim no external effects. V1/v2 manifests remain historical.
