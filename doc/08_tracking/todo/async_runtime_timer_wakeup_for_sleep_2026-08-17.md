# TODO: std.async.runtime cannot wake clock-based (timer/sleep) futures

**Filed:** 2026-08-17 | **Area:** lib/async | **Type:** runtime-integration gap
**Status:** DONE 2026-08-18 — Runtime now owns a deadline timer list.
`Runtime.spawn_sleep(millis)` (plus module-level `spawn_sleep` on the global
runtime) registers a `TimerEntry(deadline_us, task_id)`; `run_once()` fires due
timers (swapping the task's Pending future for a Ready one — `Future` is a
fixed poll result, so re-polling can never make it Ready) and, when nothing is
runnable, parks the OS thread until the NEAREST deadline (run_sleepers idiom,
no busy-spin, no new externs). Spec:
`test/01_unit/lib/async/runtime_timer_sleep_spec.spl` (4/4: >=N ms, overlap
elapsed << sum, sleep(0) prompt); `sleep_go_style_spec.spl` still 6/6.
Sabotage-verified: neutering the timer fire makes the spec hang red (timeout).
Item 2 below (poll-closure Future / pollable trait objects for storing
SleepFuture as Future<()>) remains open.

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
