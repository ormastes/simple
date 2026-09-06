# SOSIX sync leg never released its ring slot on return

**Date:** 2026-09-05 · **Status:** CLOSED (same day) · **Lane:** `.spipe/sosix_runtime_unification/state.md`

## Defect

`src/lib/nogc_async_mut/sosix/sync.spl` `_wait_for` returned the completion
value but never called `fs.release(submit.operation)`, so the slot stayed
COMPLETED-but-leased. On a capacity-1 ring the second synchronous call was
rejected with `SOSIX_ERROR_QUEUE_FULL`; on any ring the capacity was consumed
one call at a time until every sync call failed.

Found by the perf spec: the unified-read loop transferred 16 bytes on the first
iteration only.

## Fix

`sync.spl:92-94` — after the wait loop, a COMPLETED decision releases the lease
(the caller holds the result value; the lease ends with the call). Timed-out and
canceled outcomes deliberately keep the slot owned by `fs` (their buffer is still
in flight), which `fs_sync_spec` "reports a native wait timeout…" pins with
`occupancy == 1`.

## Specs

- Reproducing: `test/01_unit/lib/nogc_async_mut/sosix/fs_sync_spec.spl`
  "returns the ring slot when the synchronous call returns…" (red 5/6 before, 6/6 after).
- Generalization: `test/05_perf/lib/sosix_hosted_fs_perf_spec.spl`
  "performs exactly one ring hop per unified read…" (64 consecutive sync reads on a
  capacity-1 ring through the real file driver; `occupancy == 0` after) and
  `file_driver_spec` round-trip (write then read on one ring).
