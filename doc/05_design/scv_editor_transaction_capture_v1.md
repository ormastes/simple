# SCV Editor Transaction Capture V1

## Purpose

This slice consumes complete records from the existing SCV editor IPC spool
and returns typed editor proposals with fixed origin `ide`. It makes the
spool prefix stable and bounded before using the existing IPC state machine.
It does not publish filesystem events, update the SCV event journal, or claim
that an editor request changed a file.

## API and flow

`scv_editor_capture_open_v1(spool_path)` creates a process-local cursor.
`scv_editor_capture_poll_v1(state)` performs one bounded no-follow byte read
(maximum 1 MiB), checks UTF-8 and the previously verified prefix, and accepts
only newline-terminated records (maximum 32,768 records). A trailing partial
record stays pending and can complete on a later poll. A changed or shortened
accepted prefix poisons the cursor and returns `needs_reconciliation`.

The strict line decoder is shared from `editor_ipc.spl`; the new
`scv_editor_ipc_apply_prefix_v1` applies only the exact complete prefix passed
by the caller and does not reopen the spool. It uses the existing event DTO
and IPC state machine. Validation completes before application, so a malformed
suffix cannot partially update accepted buffers. Open save paths and refactor
markers are tracked across polls. Unmatched or nested markers, a disconnect
inside a transaction, ambiguous rename into an open buffer, malformed fields,
invalid escapes, unknown kinds, invalid UTF-8, read refusal, or bound overflow
return no new events and require reconciliation.

## Authority boundary

Every result says `proposed_only = true`. Buffer contents, save brackets,
path renames, and grouped refactor descriptors are editor assertions. A
watcher or an independent stable file read must establish the corresponding
filesystem effect before a host can record a committed event. Journal writes,
durable acknowledgements, and replay are outside this module.

The state cursor is process-local. Reopening the adapter can re-export prior
records as proposals; this V1 does not mint stable event IDs or provide
crash-safe replay receipts. The existing wire format also lacks buffer
versions, edit byte ranges, before/after content identities, editor actor
incarnations, and immutable binary payloads. It carries text payloads only.
No live IDE caller is wired to this adapter in this change.

## Acceptance scenarios

The unit and system SSpecs cover complete append and repeated poll, a split
final line, process restart replay limits, prefix rewrite/truncation,
malformed and unknown records, all-or-nothing rejection, save/refactor markers
across poll boundaries, unsaved bytes, ambiguous rename, disconnect handling,
and the absence of journal or filesystem mutation. Runtime execution was not
available for this worktree; these scenarios remain `NOT_RUN` until an
admitted Pure Simple runtime is supplied.

## Requirements traced here

- `REQ-SCV-EDITOR-CAPTURE-01`: bounded complete-record intake with cursor
  deduplication and explicit pending state.
- `REQ-SCV-EDITOR-CAPTURE-02`: malformed, ambiguous, changed-prefix, and
  incomplete transaction input fails closed and requests reconciliation.
- `REQ-SCV-EDITOR-CAPTURE-03`: editor reports remain proposals and do not
  mutate disk or the durable event journal.
