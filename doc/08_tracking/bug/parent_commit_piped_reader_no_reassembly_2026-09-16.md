# parent_commit_piped_result_reader_v1 does not reassemble split stdout chunks

Date: 2026-09-16
Status: OPEN

## Observed

`parent_commit_piped_process_spec.spl` — 2 examples fail
(`reassembles a child result split across stdout reads`,
`keeps complete later lines pending at the parent scheduling budget`).
Minimal repro (task 7, payload 707, 245-byte line split at 122/123):

- `receive_stdout_chunk(part1)` → ok, accepted=0 (expected)
- `receive_stdout_chunk(part2)` → ok, accepted=0 — the completed line is never
  accepted as a frame
- `inbox.receive()` → ok=false, empty frame (spec expects the reassembled
  `piped_child_frame(7, 707)`)

Each half is accepted without error but the concatenation never produces a
frame, so reassembly across chunk boundaries is broken (likely the pending
bytes are not carried into the next chunk's line scan).

## Impact

Any child stdout delivered in more than one read loses its result envelope at
the parent.

## Expectation

A frame line split across consecutive stdout chunks is reassembled and
delivered exactly once to the parent commit inbox.

## Unblock condition

Fix pending-buffer carry-over in
`src/lib/nogc_async_mut/parent_commit_piped_process.spl`
(`parent_commit_piped_result_reader_v1.receive_stdout_chunk`). Re-run the spec.
