# REQ-015 Environment Interaction Matrix Audit

Audit date: 2026-08-22. Scope is executable adapters and assertions, not enum
declarations or design prose.

| Interaction | Executable evidence | State |
|---|---|---|
| file | bounded open/read/close session; bounded write; exact replay | covered |
| stream | prepared bounded read; caller-owned bounded write; exact replay | covered |
| process | prepared spawn, ordered polls, kill, duplicate rejection | covered |
| environment | captured `EnvironmentGet`, exact key/value binding | partial |
| clock | capture-once `ClockRead`, nondeterminism authority, replay | partial |
| randomness | secure caller-buffer entropy plus replay and reuse rejection | covered |
| socket | loopback open/send/receive/close transcript and replay | covered |
| interrupt | mask/ack grant, pending state, read-once token, replay | covered |
| MMIO | bounded aligned read/write grant, side-effect policy, replay | covered |
| DMA | map/submit/poll/unmap lifecycle, direction/bounds, replay | covered |

Remaining concrete gaps:

- Environment and clock captures are sealed and do not reread ambient state,
  but their adapters do not yet carry a one-consumption parent cursor. A stale
  canonical cursor can produce the same applied receipt more than once.
- The hosted stream-write adapter commits to a caller-owned environment model;
  concrete pipe/terminal/device owners still need their own bounded commit
  ports when those scenarios become eligible fixtures.
- File path admission is pathname-based under a trusted fixture root. Hostile
  shared directories remain excluded until a descriptor-relative no-follow
  facade exists.

The hot paths added for file lifecycle and stream write contain no storage
construction, resize, formatting, file reread, or process spawn. They use
fixed scalar cursors and bounded copies into caller-owned regions, and their
receipts assert `allocation_count_after_seal == 0`.
