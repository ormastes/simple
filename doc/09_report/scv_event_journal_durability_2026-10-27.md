# SCV event journal durability fix

Date: 2026-10-27  
Source: `src/lib/scv/journal.spl`, `src/lib/scv/sj_capsule.spl`,
`src/lib/scv/stabilize.spl`, and `src/app/scv/main.spl`  
Tests-first commits: `e7e74fdf4e4`, `d2d9c193c00`, `e5e90ab0696`,
`35e7aa1fbfe`, `eda8decf9c2`, `439a69bf4b5`, `5a405f9beba`,
`840ac5bdd19`, `40001a42f36`

## Change

Journal and pending-batch writes now serialize through one persistent OS file
lock. Writes use no-follow regular-file reads, durable file and parent-directory
sync, and exact readback. Immutable batch seals and committed markers use a
synced private staging file and no-replace publication. Event rows publish as
one atomic replacement of the existing log, with legacy `op`, `kind`, `refs`,
`sha`, and `utc` fields retained and transaction/event identity suffixes added.

A seal binds the canonical pending payload, count, fixed timestamp, and every
expected row. Replay checks exact event identities and payloads, re-syncs the
seal/log/marker before acknowledging a committed batch, and removes the pending
file only after terminal-marker verification. Unverifiable legacy
`committed utc=...` markers are not treated as verified commits. `sj_capsule`
records its complete event list in one atomic pending write and reports record
or commit failure. Direct event callers and the event-replay CLI propagate
write/recovery failures.

## Limits

- The path APIs do not retain a directory descriptor. This code requires a
  host-controlled private SCV tree and cooperating writers; it does not claim
  protection from hostile ancestor swaps or non-cooperating writers.
- Pending batches do not have per-call stable IDs when recorded one event at a
  time. Commit/replay is idempotent by batch payload and event identity, but a
  caller that loses a successful single-record acknowledgment must reconcile
  the pending file before retrying. `sj_capsule` uses the all-at-once API.
- Legacy unmarked or partial rows for a pending batch fail closed for manual
  repair. Legacy readers still recognize the unchanged event-row prefix.
- No injected fsync failure test was available. Fault points cover crashes
  after pending, seal, event-log, and terminal-marker durability boundaries.
- Log reads and atomic rewrites are bounded at 256 MiB. Verification scans the
  current log for each expected event ID, so work grows with batch size and log
  size.

## Verification

- Tests-first SSpec regressions are committed in the preceding commits.
- Runtime SSpec execution: **NOT_RUN**; this worktree has no `bin/simple`.
- `spipe-docgen`: **NOT_RUN** for the same reason; the existing generated
  manual remains stale until generated from the updated source.
- Rust seed tests and bootstrap tests: **NOT_RUN**.
- Higher-capability source review: **PASS**, cycle 4, under the limits above.
- `git diff --check`: **PASS**.
