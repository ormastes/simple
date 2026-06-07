# EventLoop Specification

> Tests for `EventLoop` in `src/lib/gc_async_mut/gpu/browser_engine/script/event_loop.spl` (REQ-4 / AC-3). All specs FAIL until that module is implemented.

<!-- sdn-diagram:id=event_loop_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=event_loop_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

event_loop_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=event_loop_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `EventLoop` in
`src/lib/gc_async_mut/gpu/browser_engine/script/event_loop.spl` (REQ-4 / AC-3).
All specs FAIL until that module is implemented.

## Key Behaviors

- `EventLoop.new()` creates an empty event loop with no pending timers.
- `schedule_raf(callback_id)` registers a callback for the next rAF slot.
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val el = _make_empty_loop()
val count = el.pending_timer_count()
expect(count).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: AC-3: new event loop has zero pending rAF callbacks</summary>

#### AC-3: new event loop has zero pending rAF callbacks

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val el = _make_empty_loop()
val count = el.pending_raf_count()
expect(count).to_equal(0)
```

</details>


</details>

### AC-3: rAF scheduling

#### AC-3: schedule_raf increments pending rAF count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val el = _loop_with_one_raf()
val count = el.pending_raf_count()
expect(count).to_equal(1)
```

</details>

#### AC-3: two schedule_raf calls produce count of 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val el = _loop_with_two_rafs()
val count = el.pending_raf_count()
expect(count).to_equal(2)
```

</details>

### AC-3: timer cancellation

#### AC-3: cancel_timer on absent id leaves timer count unchanged

1. el cancel timer
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val el = _make_empty_loop()
el.cancel_timer(999)
val count = el.pending_timer_count()
expect(count).to_equal(0)
```

</details>

### AC-3: macrotask ordering — timers fire only after deadline

#### AC-3: timer with future deadline does not increment expired count before tick

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val el = _make_empty_loop()
# A timer set 10 seconds in the future should not have fired yet
val future_us = 10000000000
val fired = el.expired_timer_count_before(future_us)
expect(fired).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
