# EventLoop retained-work bound

> **Manual status:** `docgen-pending` — this is a complete manual mirror of
> the executable SSpec, maintained manually because the local runtime cannot
> complete its ABI probe. Regenerate with `bin/simple spipe-docgen
> test/01_unit/browser_engine/script/event_loop_spec.spl --output doc/06_spec
> --no-index` when a usable pure-Simple runtime is available.

**Traceability:** REQ-WEB-BROWSER-017, NFR-WEB-BROWSER-006.

## Scope

`EventLoop` owns the browser SimpleScript timer and animation-frame queues.
The queues retain callback identifiers until their deadline or frame drain, so
they must reject excess work at the owner boundary even when a caller does not
use `SimpleScriptExecutor`.

## Security and performance contract

- Each timer queue and animation-frame queue retains at most 256 entries.
- A timer registration at capacity returns `-1` and leaves the queue unchanged.
- An animation-frame registration at capacity is dropped; existing callbacks
  still run and a drained frame accepts newly requested animation work.
- Draining a queue releases its retained callback identifiers. Animation is
  deliberately not disabled.

## Executable evidence

`test/01_unit/browser_engine/script/event_loop_spec.spl`

| Scenario | Steps | Oracle |
| --- | --- | --- |
| `SEC-RAF-001` | Queue 257 frame callbacks, drain, schedule another callback | Pending count stays at 256; the drain returns 256; the next frame accepts one callback. |
| `SEC-TIMER-001` | Queue 257 future timers | Pending count stays at 256 and the final registration returns `-1`. |

These scenarios exercise the shared owner directly, which covers timer API and
any future host caller that bypasses higher-level executor admission checks.

## Complete executable mirror

```simple

use std.spec.*
use std.gc_async_mut.gpu.browser_engine.script.event_loop.{
    EventLoop, EVENT_LOOP_MAX_PENDING_TASKS, event_loop_clock_micros
}

# ===========================================================================
# Helper functions
# ===========================================================================

fn _make_empty_loop() -> EventLoop:
    return EventLoop.new()

fn _loop_with_one_raf() -> EventLoop:
    var el = EventLoop.new()
    el.schedule_raf(42, 0, 0)
    return el

fn _loop_with_two_rafs() -> EventLoop:
    var el = EventLoop.new()
    el.schedule_raf(10, 0, 0)
    el.schedule_raf(20, 5000, 0)
    return el

# ===========================================================================
# Specs
# ===========================================================================

describe "EventLoop":
    describe "AC-3: creation":
        it "AC-3: new event loop has zero pending timers":
            val el = _make_empty_loop()
            val count = el.pending_timer_count()
            expect(count).to_equal(0)

        it "AC-3: new event loop has zero pending rAF callbacks":
            val el = _make_empty_loop()
            val count = el.pending_raf_count()
            expect(count).to_equal(0)

    describe "AC-3: rAF scheduling":
        it "AC-3: schedule_raf increments pending rAF count":
            val el = _loop_with_one_raf()
            val count = el.pending_raf_count()
            expect(count).to_equal(1)

        it "AC-3: two schedule_raf calls produce count of 2":
            val el = _loop_with_two_rafs()
            val count = el.pending_raf_count()
            expect(count).to_equal(2)

        it "SEC-RAF-001: should bound adversarial rAF registration without disabling animation":
            step("Queue callbacks beyond one frame's retained work budget")
            var el = EventLoop.new()
            var i = 0
            while i < EVENT_LOOP_MAX_PENDING_TASKS + 1:
                el.schedule_raf(i, 0, 0)
                i = i + 1
            expect(el.pending_raf_count()).to_equal(EVENT_LOOP_MAX_PENDING_TASKS)
            step("Drain the frame and admit a later animation callback")
            expect(el.drain_raf(16000).len()).to_equal(EVENT_LOOP_MAX_PENDING_TASKS)
            el.schedule_raf(999, 16000, 0)
            expect(el.pending_raf_count()).to_equal(1)

        it "should align staggered callbacks and defer nested work to the next frame":
            step("Register staggered callbacks before one document frame")
            var el = EventLoop.new()
            el.schedule_raf(10, 0, 0)
            el.schedule_raf(20, 5000, 0)
            expect(el.next_due_micros()).to_equal(16000)
            expect(el.drain_raf(15000).len()).to_equal(0)

            step("Drain both callbacks at their shared boundary")
            val first = el.drain_raf(16000)
            expect(first.len()).to_equal(2)
            expect(first[0]).to_equal(10)
            expect(first[1]).to_equal(20)

            step("Register nested work after dispatch for the following frame")
            el.schedule_raf(30, 16000, 0)
            expect(el.next_due_micros()).to_equal(32000)
            expect(el.drain_raf(31999).len()).to_equal(0)
            val second = el.drain_raf(32000)
            expect(second.len()).to_equal(1)
            expect(second[0]).to_equal(30)

        it "should keep an unrepresentable browser clock boundary pending":
            step("Convert and schedule beyond the final representable frame")
            val maximum = 9223372036854775807
            val now = event_loop_clock_micros(maximum)
            var el = EventLoop.new()
            el.schedule_raf(40, now, now)
            expect(now).to_equal(maximum)
            expect(el.next_due_micros()).to_equal(-1)
            expect(el.drain_raf(maximum).len()).to_equal(0)
            expect(el.pending_raf_count()).to_equal(1)

    describe "SEC-TIMER-001: timer queue retention":
        it "should reject a timer beyond the retained task budget":
            step("Queue timers beyond the shared event-loop work budget")
            var el = EventLoop.new()
            var i = 0
            var last_id = 0
            while i < EVENT_LOOP_MAX_PENDING_TASKS + 1:
                last_id = el.schedule_timer(i, 1000000, 0)
                i = i + 1
            expect(el.pending_timer_count()).to_equal(EVENT_LOOP_MAX_PENDING_TASKS)
            expect(last_id).to_equal(-1)

    describe "AC-3: timer cancellation":
        it "AC-3: cancel_timer on absent id leaves timer count unchanged":
            val el = _make_empty_loop()
            el.cancel_timer(999)
            val count = el.pending_timer_count()
            expect(count).to_equal(0)

    describe "AC-3: macrotask ordering — timers fire only after deadline":
        it "AC-3: timer with future deadline does not increment expired count before tick":
            val el = _make_empty_loop()
            # A timer set 10 seconds in the future should not have fired yet
            val future_us = 10000000000
            val fired = el.expired_timer_count_before(future_us)
            expect(fired).to_equal(0)
```

The executable source's module documentation is reproduced by this manual's
scope and contract sections; its executable code is mirrored above verbatim.

## Run

```sh
bin/simple test test/01_unit/browser_engine/script/event_loop_spec.spl --mode=interpreter
```

The local deployed runtime must pass its ABI probe before this command can run.
