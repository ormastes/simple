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
