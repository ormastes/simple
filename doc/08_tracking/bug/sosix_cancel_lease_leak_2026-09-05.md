# SOSIX cancel of a committed submission leaked the ring lease

**Date:** 2026-09-05 · **Status:** CLOSED (same day) · **Lane:** `.spipe/sosix_runtime_unification/state.md`

## Defect

`SimpleRing.cancel` on a Committed/InFlight slot only sets `cancel_requested`
and answers `ProviderCancelRequested`; the provider must then publish the
`Cancelled` terminal, because `_complete` refuses every other kind with
`CancellationRequired` (`simple_ring.spl:426`). `SosixHostedFs.service_one`
always published success, so the completion was refused, the slot stayed
InFlight, `retired[slot]` never flipped, and `release` was refused forever.

## Fix

`fs.spl` `take_next` answers a cancel-requested submission with
`complete_cancelled` and reports it as not taken; `pump` retires a locally
CANCELED slot without a second completion. `sync.spl` `_result` now maps a
canceled native wait to `SOSIX_ERROR_CANCELED` (was reported as a timeout).

## Specs

- Reproducing: `fs_async_spec` "retires a canceled submission so its slot can be
  released" (6/7 before, 7/7 after; sabotage arm with the branch disabled: 6/7).
- Generalization: `fs_sync_spec` "reports a canceled native wait as canceled, not
  as a timeout" (adjacent path: the sync leg's outcome mapping).
