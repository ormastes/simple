# Async-tier mutex/rwlock have no async-suspend locking (block the carrier OS thread)

- **Date:** 2026-07-28
- **Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)
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

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
