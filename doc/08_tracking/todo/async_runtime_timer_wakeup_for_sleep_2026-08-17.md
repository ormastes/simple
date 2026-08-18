# TODO: std.async.runtime cannot wake clock-based (timer/sleep) futures

**Filed:** 2026-08-17 | **Area:** lib/async | **Type:** runtime-integration gap

## Gap
`std.async.runtime.Runtime.run_once()` re-enqueues tasks only via
`waker_signal`/`waker_check` (`src/lib/nogc_async_mut/async/runtime.spl:97-106`),
and `Future.pending()` stays pending forever. There is no timer backend that
signals a waker when a deadline passes, so a task suspended on
`AsyncIO.sleep()` (a stub returning `Future.pending`, see
`src/lib/nogc_async_mut/async/io.spl:38-50`) is never resumed by the Runtime.

## What exists now (pure Simple, landed with this todo)
`src/lib/nogc_async_mut/async/sleep.spl` provides the Go-style surface:
`sleep(ms) -> SleepFuture` (poll-based deadline future, microsecond clock),
`await_sleep`, `run_sleepers([...])` (cooperative mini-scheduler that drives N
sleepers concurrently and parks the OS thread only until the NEAREST deadline),
and `sleep_blocking(ms)` as the no-scheduler fallback. Spec:
`test/01_unit/lib/async/sleep_go_style_spec.spl` (proves overlap: two 60ms
sleeps complete in <110ms total).

## What is still missing
1. Runtime-owned timer wheel/heap: `Runtime` should accept
   `(task_id, deadline)` registrations and, when the ready queue is empty,
   sleep until the nearest deadline and then `waker_signal` the task —
   making `AsyncIO.sleep()` real instead of a stub.
2. `SleepFuture` cannot be stored as `Future<()>` today because `Future` has no
   poll-closure variant; either add one or teach TaskContext to hold pollable
   trait objects (composition, no inheritance).
