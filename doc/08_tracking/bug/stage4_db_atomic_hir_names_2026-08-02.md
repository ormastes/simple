# Stage4 atomic-database HIR names

**Status:** OPEN (unverified 2026-09-12)

## Reproduction

Stage4 HIR lowering stopped in `nogc_async_mut/db_atomic.spl` with unresolved
file, lock, process, time, and `_` names.

## Fix

Both no-GC database mirrors import file operations, process identity, and time
from their concrete owner modules. The async mirror now uses the same `?`
Result propagation as the sync implementation instead of matching `Ok(_)`,
which Stage4 treated as an unresolved identifier.

## Regression evidence

`db_atomic_hir_contract_spec.spl` checks concrete owners, removal of the broad
facade import, native-safe propagation, and sync/async mirror parity.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.

## Triage 2026-09-13 (BUGFIX-7 lane)

Out of lane: needs a Stage4 HIR-lowering bootstrap run to reproduce/verify. No change made.
## Triage 2026-09-13 (BUGFIX-11)

Ran the doc's own named regression spec on the deployed seed
(`/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
50,093,192 B, 2026-09-06 09:59):

```
$ bin/simple test test/01_unit/lib/db_atomic_hir_contract_spec.spl --no-cache --no-cover-check
✗ a locked atomic write is readable back byte-for-byte in the sync mirror
✗ an atomic update transforms content under the lock in the sync mirror
✓ reading a missing file yields empty content rather than an error
✗ the async mirror satisfies the same write/read/update behavior
4 examples, 3 failures
```

This is NOT the original Stage4-HIR-unresolved-identifier symptom this doc
is filed under — no "unresolved name"/HIR-lowering error appears; the spec
compiles and runs under the interpreter without issue, which is consistent
with the doc's own claimed fix (async mirror uses `?` propagation instead of
`Ok(_)` pattern matching) actually being present in
`src/lib/nogc_async_mut/db_atomic.spl` today. What is broken instead is a
distinct, functional read/write contract failure: a write through the lock
is not read back byte-for-byte in either the sync or async mirror. Not
triaged further (needs stepping through `db_atomic.spl`'s lock/write/read
path, which is beyond the 5-minute/45-minute budget for this pass). Left
OPEN. Fix direction for the next lane: start from
`test/01_unit/lib/db_atomic_hir_contract_spec.spl`'s three failing
assertions and trace the write-then-read path in
`src/lib/nogc_async_mut/db_atomic.spl` (and its sync counterpart) to find
where the written content is lost or not flushed before the read.
