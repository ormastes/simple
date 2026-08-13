# Async runtime: detached completed results have no bounded consumption contract

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
