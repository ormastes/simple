# Async-tier mutex/rwlock have no async-suspend locking (block the carrier OS thread)

- **Date:** 2026-07-28
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Area:** src/lib/nogc_async_mut/concurrent/{mutex,rwlock}.spl

## Summary

The `nogc_async_mut` mutex/rwlock modules are facades re-exporting the sync
backend (`src/lib/nogc_sync_mut/concurrent/`). `lock()` / `with_lock()` /
`with_write()` therefore **block the calling OS thread** (rt_mutex_lock is an
atomic-flag spin loop in `src/runtime/runtime_native.c`). Under the green-thread
scheduler, a contended lock stalls every task multiplexed on that carrier
thread instead of suspending only the waiting task.

## Wanted

Async-aware locking: on contention, park the current green thread and resume it
on unlock (scheduler integration in
`src/lib/nogc_async_mut/concurrent/green_thread.spl` / runtime hooks). Until
then the sync-backed facade is intentional and loudly documented in both facade
files — do not remove the warning without implementing suspend semantics.

## Re-verification 2026-08-17 (stdlib slice G, content-classified)

**STILL-OPEN, confirmed by CONTENT and deliberate.**
`src/lib/nogc_async_mut/concurrent/mutex.spl:18` is a single
`export use std.nogc_sync_mut.concurrent.mutex.{...}` re-export, and the module
docstring (lines 4-9) states plainly: "This tier has NO async-aware mutex:
`lock()`/`with_lock()` spin/block". The described behaviour is the current, stated
design; this is a feature gap, not a silent-wrong-result defect. No stdlib-local
fix is possible without an async-aware backend.
