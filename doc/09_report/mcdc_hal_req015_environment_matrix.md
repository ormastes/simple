# REQ-015 Environment Interaction Matrix Audit

Audit date: 2026-08-22. Scope is executable adapters and assertions, not enum
declarations or design prose.

| Interaction | Executable evidence | State |
|---|---|---|
| file | pinned capability-root descriptor, descriptor-relative no-follow open/read/write/close, exact replay | covered |
| stream | prepared bounded read; caller-owned bounded write; exact replay | covered |
| process | prepared spawn, ordered polls, kill, duplicate rejection | covered |
| environment | captured `EnvironmentGet`, exact key/value binding, one-consumption parent cursor | covered |
| clock | capture-once `ClockRead`, nondeterminism authority, one-consumption replay cursor | covered |
| randomness | secure caller-buffer entropy plus replay and reuse rejection | covered |
| socket | loopback open/send/receive/close transcript and replay | covered |
| interrupt | mask/ack grant, pending state, read-once token, replay | covered |
| MMIO | bounded aligned read/write grant, side-effect policy, replay | covered |
| DMA | map/submit/poll/unmap lifecycle, direction/bounds, replay | covered |

Remaining concrete gaps:

- Environment and clock captures now use the same one-consumption parent
  cursor discipline as the other replay adapters; duplicate consumption fails
  closed. End-to-end extraction from an executing tagged `rt(hal)` test still
  requires the sealed provider result/session binding described in
  `doc/09_report/rt_hal_clock_sealed_result_binding_2026-08-22.md`.
- The hosted stream-write adapter commits to a caller-owned environment model;
  concrete pipe/terminal/device owners still need their own bounded commit
  ports when those scenarios become eligible fixtures.
- Hostile shared-directory file access now pins the capability-root descriptor
  before sealing, rejects absolute/parent/symlink traversal, verifies the final
  descriptor is a regular file, and uses positional caller-buffer I/O. Native
  evidence replaces the root pathname after pinning and proves access remains
  on the original inode tree (`check-hosted-confined-file.shs`).

The hot paths added for file lifecycle and stream write contain no storage
construction, resize, formatting, file reread, or process spawn. They use
fixed scalar cursors and bounded copies into caller-owned regions, and their
receipts assert `allocation_count_after_seal == 0`.
