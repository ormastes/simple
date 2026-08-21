# SimpleOS SFTP fragment accumulator has quadratic copy cost

Status: IMPLEMENTED — admitted-runtime evidence remains release-blocking for REQ-015, REQ-016, and NFR-002.

## Defect

`SftpSessionV3` is now the sole mutable accumulator owner. New fragments append
directly to its bounded retained array; compaction occurs only after a complete
frame is consumed. A retained prefix is no longer copied on each fragment, so
one-byte fragmentation performs amortized linear append work.
The production owner publishes `SftpAccumulatorWorkV3`; its focused one-byte
fragment scenario records 9 admitted ingress bytes, 18 actual copied bytes (append plus
one admitted frame copy), 24 header-scan bytes, one completed frame, and a
9-byte peak. Counters saturate without changing protocol behavior.

The associated correctness blockers are also implemented:

- `SftpSessionV3.new` is the minimum public constructor; internal fields remain
  private.
- `SshSession.run` now enters the one canonical `do_interactive` implementation
  in `ssh_session_channel.spl`. Exact `subsystem`/`sftp` requests bind the SFTP
  owner to one channel, and only that channel's bounded data reaches the parser.

The bounded continuation reached its mandatory three verify/fix cycles after
repairing value-state persistence, split/coalesced framing, and SSH window
accounting. This remaining performance defect is therefore recorded rather
than retried in the same session.

The duplicate alternate handler was removed. `ssh_session.spl` owns lifecycle,
authentication, and transport; `ssh_session_channel.spl` owns the cohesive live
channel methods. Both are below 800 lines and mutate the same `SshSession`
instance rather than competing state roots.

## Required closure

- Run the focused SFTP spec and the REQ-015/REQ-016 system evidence with an
  admitted self-hosted Simple runtime.

Owner: SSH/SFTP service lane.
Final reviewer: independent SimpleOS hardening verifier.

## Runtime evidence 2026-08-21

Binary: `bin/release/x86_64-unknown-linux-gnu/simple` (Rust bootstrap seed).
Self-hosted admission still outstanding — a full bootstrap was running
concurrently in this worktree.

- First run: `Results: 9 total, 8 passed, 1 failed`. The failure was NOT the
  accumulator: `rejects traversal without filesystem access` died with
  `semantic: class SshStringResult has no field named value`.
  Root cause in `src/os/apps/sshd/ssh_sftp_v3.spl:204` — it called
  `ssh_get_string` (returns `SshStringResult.data: [u8]`) and then read
  `.value`, while `_path_safe` takes `text`. The path-traversal guard had
  therefore never compiled or run. Fixed by calling `ssh_get_text`
  (returns `SshTextResult.value: text`) and adjusting the import.
- After fix: `Results: 9 total, 9 passed, 0 failed` /
  `SPEC FILE VERDICT: ... executed=9 passed=9 failed=0 skipped=0 dropped=0` /
  `PASS test/01_unit/os/apps/sshd/ssh_sftp_v3_spec.spl`.
- Accumulator scenarios green: `accepts a complete frame fragmented one byte
  at a time`, `retains a split length header`, `retains a coalesced second
  frame`.
- Source re-verified: `_append` writes each byte once at
  `(rx_head + rx_count) % SFTP_ACCUMULATOR_CAP`; `handle_packet` consumes by
  advancing `rx_head` and never copies the retained remainder. Amortized
  linear append confirmed.

**Neighbors:** the transport that FEEDS this owner is still quadratic —
`ssh_session.spl:683,707,718` concatenates `recv_buf` per fragment. Recorded
with five other sites in
`doc/08_tracking/bug/networking_fragment_accumulator_quadratic_neighbors_2026-08-21.md`.

**Still open:** REQ-015/REQ-016 system evidence on an admitted self-hosted runtime.
