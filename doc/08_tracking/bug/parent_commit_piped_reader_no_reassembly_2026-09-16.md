# parent_commit_piped_result_reader_v1 does not reassemble split stdout chunks

Date: 2026-09-16
Status: FIXED 2026-11-11 (P3 lane ne19 triage, release/1.0.0 worktree)

## Addendum 2026-11-11 (lane ne19) — FIXED, verified by execution

The pending-buffer carry-over this doc's unblock condition asked for is
present in `src/lib/nogc_async_mut/parent_commit_piped_process.spl`
(`receive_stdout_chunk`): the line scan now runs over `val input =
self.pending + chunk` with `self.pending` retained across calls and the
partial trailing line re-saved after the scan.

Executed on the release/1.0.0 worktree seed binary
(`bin/simple.exe`, self-identified Rust bootstrap seed v1.0.0-rc.1):

    bin/simple.exe test test/01_unit/lib/nogc_async_mut/parent_commit_piped_process_spec.spl
    outcome=OK declared>=6 executed=6 passed=6 failed=0

Both examples named in this doc ("reassembles a child result split across
stdout reads", "keeps complete later lines pending at the parent scheduling
budget") exist in the spec and pass. No code change in this lane; the fix
predates this triage and is now evidenced.

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
