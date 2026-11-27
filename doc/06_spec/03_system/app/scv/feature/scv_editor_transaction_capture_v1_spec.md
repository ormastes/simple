# SCV editor transaction capture V1

Source: `test/03_system/app/scv/feature/scv_editor_transaction_capture_v1_spec.spl`.
Audience: SCV and editor adapter maintainers.

Execution: **NOT_RUN**. The test-first BDD scenarios are authored, but this
worktree has no admitted Pure Simple runtime or spec doc generator. This
manual is a review aid, not a generated or executed SPipe receipt.

## Prefix intake and cursor behavior

The adapter reads a bounded UTF-8 spool, accepts only complete newline-ended
records, and retains the last verified prefix. A partial final record remains
pending until the writer appends its newline. Polling the same state against an
unchanged prefix emits nothing twice. Opening a new state over an existing
spool can reread prior proposals; V1 has no stable event ID or durable replay
receipt.

A complete-prefix rewrite or truncation poisons the cursor. Malformed escape
sequences, wrong field counts, unknown record kinds, unmatched or nested save
and refactor markers, ambiguous rename into an open buffer, and disconnect
during an open transaction return `needs_reconciliation` with no events from
the invalid batch. Earlier accepted buffer bytes remain intact.

## Proposed events and effects

Open and edited buffer contents are retained as editor proposals. Save markers
must match, and refactor entity hints are grouped only by a matching begin/end
pair, including pairs that span polls. A rename is a hint: it does not rename a
disk file. The adapter leaves the event journal unchanged. A caller must
independently observe filesystem results before recording committed effects.

The inherited wire format does not bind editor buffer versions, byte offsets,
before/after content identities, actor incarnations, or immutable binary
payloads. This V1 validates transport records and cursor continuity only; it
does not establish those missing facts or connect a live IDE caller.
