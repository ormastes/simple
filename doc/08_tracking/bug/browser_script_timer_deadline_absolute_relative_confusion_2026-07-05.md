# Browser script setTimeout/setInterval deadline logic fires timers on first tick regardless of delay

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Status
Implementation fixed; executable BrowserSession regression is compiler-blocked.

## Severity
High — logic error, latent (currently unreachable, but will break core timing semantics the moment JS timers/rAF are wired into a live page).

## Summary
`src/lib/gc_async_mut/gpu/browser_engine/script/timer_api.spl:23-39` computes `deadline = ms * 1000` (relative delay in microseconds) and passes it directly to `loop_ref.schedule_timer()`, treating it as an absolute deadline. However, `EventLoop.drain_expired()` in `script/event_loop.spl:67-100` compares `deadline_micros <= now_micros` where `now_micros` is a real wall-clock value (~10^15). Since `ms*1000` is always vastly smaller (thousands to millions), **every `setTimeout`/`setInterval` fires on the very first `tick()` call**, regardless of requested delay.

## Evidence
- **timer_api.spl:23-39**: `set_timeout(ms)` and `set_interval(ms)` both set `deadline = ms * 1000` with no `now_micros()` base.
- **event_loop.spl:67-100**: `drain_expired(now_micros)` and `expired_timer_count_before(now_micros)` compare `deadline_micros <= now_micros` directly against real wall-clock time.
- **event_loop.spl:93**: The re-queue path for interval fires is correct: `now_micros + interval_micros`, showing the intended contract is absolute time.
- **test/01_unit/browser/script/timer_api_spec.spl**: Unit spec never invokes `drain_expired()` with a real clock value; only checks that `pending_timer_count() == 1` after scheduling, never validates firing behavior.

## Failure Scenario
A 5000ms `setTimeout` would fire "instantly" on the first call to `ScriptHost.tick()` instead of waiting 5 seconds. JS timing-based animations, debounces, and delays become non-functional; CSS/JS transitions and requestAnimationFrame scheduling depend on this path.

## Next Step
Change `deadline = ms * 1000` to `deadline = rt_time_now_unix_micros() + ms * 1000` in both `set_timeout` and `set_interval`. Add a real-clock test case to `timer_api_spec.spl` that verifies timers do not fire before the deadline when `drain_expired()` is called with a wall-clock time.

## Resolution (2026-07-26)

The legacy `TimerApi` now schedules against `rt_time_now_unix_micros()` and its
unit spec drains before and after the wall-clock deadline. A second equivalent
bug remained in the canonical BrowserSession runtime: recreating a JS
interpreter after navigation reset its timer clock to zero while the session
clock remained advanced. Both runtime creation paths now seed
`timer_current_time_ms` from `BrowserSession.monotonic_time_ms`; the integration
scenario covers a runtime created at 1000ms and a 500ms timeout due only at
1500ms. Execution remains blocked by the tracked target compiler failure.

## Queue-retention update (2026-07-29)

Both active JS interpreter variants now remove completed one-shot timers and
canceled handles directly from their bounded pending arrays; intervals replace
their selected slot in place. Due selection remains a bounded linear scan, but
draining no longer reconstructs a second queue per callback. Focused source
coverage was updated; pure-Simple runtime evidence remains compiler-blocked.
