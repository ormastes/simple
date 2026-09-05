# EventLoop Specification

> Tests for `EventLoop` in `src/lib/gc_async_mut/gpu/browser_engine/script/event_loop.spl` (REQ-4 / AC-3). All specs FAIL until that module is implemented.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# EventLoop Specification

Tests for `EventLoop` in `src/lib/gc_async_mut/gpu/browser_engine/script/event_loop.spl` (REQ-4 / AC-3). All specs FAIL until that module is implemented.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #M15-EVENT-LOOP |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/browser_engine/script/event_loop_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `EventLoop` in
`src/lib/gc_async_mut/gpu/browser_engine/script/event_loop.spl` (REQ-4 / AC-3).
All specs FAIL until that module is implemented.

## Key Behaviors

- `EventLoop.new()` creates an empty event loop with no pending timers.
- `schedule_raf(callback_id, now, origin)` aligns callbacks to a shared 16ms
  document-clock boundary.
- `cancel_timer(timer_id)` removes a pending macrotask timer.
- `pending_timer_count()` returns number of pending timers.
- `pending_raf_count()` returns number of pending rAF callbacks.
- Timers scheduled with a future deadline are not fired before their time.
- Timers scheduled with a past/current deadline fire on the next `tick`.

## Scenarios

### EventLoop

### AC-3: creation

<details>
<summary>Advanced: AC-3: new event loop has zero pending timers</summary>

#### AC-3: new event loop has zero pending timers

- AC-3: new event loop has zero pending timers
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

use std.spec.*
use std.gc_async_mut.gpu.browser_engine.script.event_loop.{
    EventLoop, EVENT_LOOP_MAX_PENDING_TASKS
}

# ===========================================================================
# Helper functions
# ===========================================================================

fn _make_empty_loop() -> EventLoop:
    return EventLoop.new()

fn _loop_with_one_raf() -> EventLoop:
    var el = EventLoop.new()
    el.schedule_raf(42)
    return el

fn _loop_with_two_rafs() -> EventLoop:
    var el = EventLoop.new()
    el.schedule_raf(10)
    el.schedule_raf(20)
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
                el.schedule_raf(i)
                i = i + 1
            expect(el.pending_raf_count()).to_equal(EVENT_LOOP_MAX_PENDING_TASKS)
            step("Drain the frame and admit a later animation callback")
            expect(el.drain_raf().len()).to_equal(EVENT_LOOP_MAX_PENDING_TASKS)
            el.schedule_raf(999)
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

</details>


</details>

<details>
<summary>Advanced: AC-3: new event loop has zero pending rAF callbacks</summary>

#### AC-3: new event loop has zero pending rAF callbacks

- AC-3: new event loop has zero pending rAF callbacks
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-3: new event loop has zero pending rAF callbacks")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val el = _make_empty_loop()
val count = el.pending_raf_count()
expect(count).to_equal(0)  # oracle: count must equal 0 — authoritative contract constant
```

</details>


</details>

### AC-3: rAF scheduling

#### AC-3: schedule_raf increments pending rAF count

- AC-3: schedule_raf increments pending rAF count
   - Expected: count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-3: schedule_raf increments pending rAF count")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val el = _loop_with_one_raf()
val count = el.pending_raf_count()
expect(count).to_equal(1)  # oracle: count must equal 1 — authoritative contract constant
```

</details>

#### AC-3: two schedule_raf calls produce count of 2

- AC-3: two schedule_raf calls produce count of 2
   - Expected: count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-3: two schedule_raf calls produce count of 2")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val el = _loop_with_two_rafs()
val count = el.pending_raf_count()
expect(count).to_equal(2)  # oracle: count must equal 2 — authoritative contract constant
```

</details>

#### SEC-RAF-001: should bound adversarial rAF registration without disabling animation

- SEC-RAF-001: should bound adversarial rAF registration without disabling animation
- Queue callbacks beyond one frame's retained work budget
   - Expected: el.pending_raf_count() equals `EVENT_LOOP_MAX_PENDING_TASKS`
- Drain the frame and admit a later animation callback
   - Expected: el.drain_raf(16000).len() equals `EVENT_LOOP_MAX_PENDING_TASKS`
   - Expected: el.pending_raf_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("SEC-RAF-001: should bound adversarial rAF registration without disabling animation")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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
expect(el.pending_raf_count()).to_equal(1)  # oracle: el.pending_raf_count() must equal 1 — authoritative contract constant
```

</details>

#### align staggered callbacks and defer nested work to the next frame

- align staggered callbacks and defer nested work to the next frame
- Register staggered callbacks before one document frame
   - Expected: el.next_due_micros() equals `16000`
   - Expected: el.drain_raf(15000).len() equals `0`
- Drain both callbacks at their shared boundary
   - Expected: first.len() equals `2`
   - Expected: first[0] equals `10`
   - Expected: first[1] equals `20`
- Register nested work after dispatch for the following frame
   - Expected: el.next_due_micros() equals `32000`
   - Expected: el.drain_raf(31999).len() equals `0`
   - Expected: second.len() equals `1`
   - Expected: second[0] equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("align staggered callbacks and defer nested work to the next frame")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Register staggered callbacks before one document frame")
var el = EventLoop.new()
el.schedule_raf(10, 0, 0)
el.schedule_raf(20, 5000, 0)
expect(el.next_due_micros()).to_equal(16000)  # oracle: el.next_due_micros() must equal 16000 — authoritative contract constant
expect(el.drain_raf(15000).len()).to_equal(0)  # oracle: el.drain_raf(15000).len() must equal 0 — authoritative contract constant

step("Drain both callbacks at their shared boundary")
val first = el.drain_raf(16000)
expect(first.len()).to_equal(2)  # oracle: first.len() must equal 2 — authoritative contract constant
expect(first[0]).to_equal(10)  # oracle: first[0] must equal 10 — authoritative contract constant
expect(first[1]).to_equal(20)  # oracle: first[1] must equal 20 — authoritative contract constant

step("Register nested work after dispatch for the following frame")
el.schedule_raf(30, 16000, 0)
expect(el.next_due_micros()).to_equal(32000)  # oracle: el.next_due_micros() must equal 32000 — authoritative contract constant
expect(el.drain_raf(31999).len()).to_equal(0)  # oracle: el.drain_raf(31999).len() must equal 0 — authoritative contract constant
val second = el.drain_raf(32000)
expect(second.len()).to_equal(1)  # oracle: second.len() must equal 1 — authoritative contract constant
expect(second[0]).to_equal(30)  # oracle: second[0] must equal 30 — authoritative contract constant
```

</details>

#### keep an unrepresentable browser clock boundary pending

- keep an unrepresentable browser clock boundary pending
- Convert and schedule beyond the final representable frame
   - Expected: now equals `maximum`
   - Expected: el.next_due_micros() equals `-1`
   - Expected: el.drain_raf(maximum).len() equals `0`
   - Expected: el.pending_raf_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("keep an unrepresentable browser clock boundary pending")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Convert and schedule beyond the final representable frame")
val maximum = 9223372036854775807
val now = event_loop_clock_micros(maximum)
var el = EventLoop.new()
el.schedule_raf(40, now, now)
expect(now).to_equal(maximum)
expect(el.next_due_micros()).to_equal(-1)  # oracle: el.next_due_micros() must equal -1 — authoritative contract constant
expect(el.drain_raf(maximum).len()).to_equal(0)  # oracle: el.drain_raf(maximum).len() must equal 0 — authoritative contract constant
expect(el.pending_raf_count()).to_equal(1)  # oracle: el.pending_raf_count() must equal 1 — authoritative contract constant
```

</details>

### SEC-TIMER-001: timer queue retention

#### reject a timer beyond the retained task budget

- reject a timer beyond the retained task budget
- Queue timers beyond the shared event-loop work budget
   - Expected: el.pending_timer_count() equals `EVENT_LOOP_MAX_PENDING_TASKS`
   - Expected: last_id equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("reject a timer beyond the retained task budget")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Queue timers beyond the shared event-loop work budget")
var el = EventLoop.new()
var i = 0
var last_id = 0
while i < EVENT_LOOP_MAX_PENDING_TASKS + 1:
    last_id = el.schedule_timer(i, 1000000, 0)
    i = i + 1
expect(el.pending_timer_count()).to_equal(EVENT_LOOP_MAX_PENDING_TASKS)
expect(last_id).to_equal(-1)  # oracle: last_id must equal -1 — authoritative contract constant
```

</details>

### AC-3: timer cancellation

#### AC-3: cancel_timer on absent id leaves timer count unchanged

- AC-3: cancel_timer on absent id leaves timer count unchanged
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-3: cancel_timer on absent id leaves timer count unchanged")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val el = _make_empty_loop()
el.cancel_timer(999)
val count = el.pending_timer_count()
expect(count).to_equal(0)  # oracle: count must equal 0 — authoritative contract constant
```

</details>

### AC-3: macrotask ordering — timers fire only after deadline

#### AC-3: timer with future deadline does not increment expired count before tick

- AC-3: timer with future deadline does not increment expired count before tick
   - Expected: fired equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("AC-3: timer with future deadline does not increment expired count before tick")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val el = _make_empty_loop()
# A timer set 10 seconds in the future should not have fired yet
val future_us = 10000000000
val fired = el.expired_timer_count_before(future_us)
expect(fired).to_equal(0)  # oracle: fired must equal 0 — authoritative contract constant
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BROWSER_ENGINE`
- `REQ-4`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5fed908dfe894124faf773422a7f63f7d906e1d9f67df3e37b87105d039df4eb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5fed908dfe894124faf773422a7f63f7d906e1d9f67df3e37b87105d039df4eb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5fed908dfe894124faf773422a7f63f7d906e1d9f67df3e37b87105d039df4eb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/01_unit/browser_engine/script/event_loop_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/script/event_loop_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/script/event_loop_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/script/event_loop_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
