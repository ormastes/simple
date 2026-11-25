# Async runtime: detached completed results have no bounded consumption contract

Status: NARROW DEFECT RESOLVED 2026-11-25 (see dated note at bottom); the
broader bounded result-domain contract remains a WP-14/WP-18 design program,
not a bug-ledger fix.
Status re-verified 2026-08-17 by source inspection (triage shard 00).

- **Date:** 2026-08-13
- **Severity:** P1 (bounded-memory contract gap)
- **Owner:** WP-14/WP-18 typed task-result runtime lanes

## Observed

`src/lib/nogc_async_mut/async/runtime.spl` retains each completed task in
`Runtime.completed`. `Runtime.block_on()` now consumes and removes its own
result, but the same runtime exposes `spawn()` without a matching admitted
join/take/cancel result lifecycle. A caller that uses detached `spawn()` can
therefore leave completed entries retained indefinitely.

The current runtime's result values are simplified text and its task transport
is not the typed transfer-envelope path. Adding an arbitrary eviction cap here
would silently discard a result with no explicit caller-visible outcome.

## Expected

The eventual task runtime needs one owner-owned, bounded result domain:

- admission reserves result capacity before work starts;
- completion publishes exactly one typed terminal outcome;
- join/take/cancel releases that reservation exactly once;
- full, closed, cancellation, and stale/double-consume states are explicit;
- high-water counters make the bound observable.

## Unblock condition

Land the WP-14/WP-18 typed task-envelope and `PoolState` lifecycle contract,
then route detached async tasks through it. Add native evidence for bounded
accepted work, result consumption, cancellation, stale handles, and repeated
create/run/destroy cycles. Do not claim that the legacy `Runtime.spawn()` is a
bounded parallel task API before those gates pass.

## Re-verification 2026-08-17 (stdlib slice G, content-classified)

**ALREADY-FIXED (verdict by CONTENT).** `src/lib/nogc_async_mut/async/runtime.spl`
now evicts: `self.completed.remove(task_id)` at :161, guarded by the
`contains_key` check at :156 and read at :158, with the in-source comment at :160
("global Runtime would otherwise leak one completed entry per call"). The
unbounded-retention path described in this doc no longer exists. Closing.

## Triage 2026-09-13
Reconfirmed via source inspection: bounded-memory contract for detached
completed results is still unimplemented per this record's own description.
Fix is a runtime design change (async task-result lifecycle), not a quick
single-file fix. Left OPEN, no code change attempted.

## Verification 2026-11-25 (p2w1-ag lane, source inspection)

The narrow retention defect filed here is resolved in current source, and
more strongly than the 2026-08-17 note describes:

- `Runtime.run_once()` now drops results for unawaited tasks entirely:
  `src/lib/nogc_async_mut/async/runtime.spl:226` gates the
  `self.completed.insert(task_id, result)` on
  `self.awaited.contains_key(task_id)`, so a detached `spawn()` leaves **no**
  completed entry behind at all (the in-source comment at :222-225 cites this
  exact bug doc).
- `Runtime.block_on()` consumes and removes its own result:
  `self.completed.remove(task_id)` at :260, with `self.awaited` cleaned up at
  :261.

So the unbounded-retention path ("a caller that uses detached `spawn()` can
leave completed entries retained indefinitely") no longer exists. The broader
"Expected" section — an owner-owned bounded result domain with admission
reservations, typed terminal outcomes, and high-water counters — is the
WP-14/WP-18 typed task-envelope design program named in the unblock
condition; it is a design lane, not a bug-ledger fix, and is out of scope for
this pass. Verified by source inspection only: spec execution at this HEAD is
blocked repo-wide by the pinned seed rejecting `@representation_boundary`
(see the 2026-11-25 note in
`check_directory_target_false_green_2026-07-24.md`).
