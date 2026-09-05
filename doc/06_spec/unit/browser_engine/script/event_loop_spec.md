# EventLoop Specification

> Tests for `EventLoop` in `src/lib/gc_async_mut/gpu/browser_engine/script/event_loop.spl` (REQ-4 / AC-3). All specs FAIL until that module is implemented.

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
| Source | `test/unit/browser_engine/script/event_loop_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `EventLoop` in
`src/lib/gc_async_mut/gpu/browser_engine/script/event_loop.spl` (REQ-4 / AC-3).
All specs FAIL until that module is implemented.

## Key Behaviors

- `EventLoop.new()` creates an empty event loop with no pending timers.
- `schedule_raf(callback_id, now, origin)` registers a callback for the next
  document-clock rAF slot.
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

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: new event loop has zero pending timers")
val el = _make_empty_loop()
val count = el.pending_timer_count()
expect(count).to_equal(0)
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

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: new event loop has zero pending rAF callbacks")
val el = _make_empty_loop()
val count = el.pending_raf_count()
expect(count).to_equal(0)
```

</details>


</details>

### AC-3: rAF scheduling

#### AC-3: schedule_raf increments pending rAF count

- AC-3: schedule_raf increments pending rAF count
   - Expected: count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: schedule_raf increments pending rAF count")
val el = _loop_with_one_raf()
val count = el.pending_raf_count()
expect(count).to_equal(1)
```

</details>

#### AC-3: two schedule_raf calls produce count of 2

- AC-3: two schedule_raf calls produce count of 2
   - Expected: count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: two schedule_raf calls produce count of 2")
val el = _loop_with_two_rafs()
val count = el.pending_raf_count()
expect(count).to_equal(2)
```

</details>

### AC-3: timer cancellation

#### AC-3: cancel_timer on absent id leaves timer count unchanged

- AC-3: cancel_timer on absent id leaves timer count unchanged
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: cancel_timer on absent id leaves timer count unchanged")
val el = _make_empty_loop()
el.cancel_timer(999)
val count = el.pending_timer_count()
expect(count).to_equal(0)
```

</details>

### AC-3: macrotask ordering — timers fire only after deadline

#### AC-3: timer with future deadline does not increment expired count before tick

- AC-3: timer with future deadline does not increment expired count before tick
   - Expected: fired equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: timer with future deadline does not increment expired count before tick")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `24a49705c1a80c6d3569b8c007b79278e33f1eb4e8d2f17a89fc99e942abe73f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `24a49705c1a80c6d3569b8c007b79278e33f1eb4e8d2f17a89fc99e942abe73f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `24a49705c1a80c6d3569b8c007b79278e33f1eb4e8d2f17a89fc99e942abe73f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/browser_engine/script/event_loop_spec.spl
mirror: doc/06_spec/unit/browser_engine/script/event_loop_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/browser_engine/script/event_loop_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/browser_engine/script/event_loop_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/browser_engine/script/event_loop_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/browser_engine/script/event_loop_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: new event loop has zero pending timers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/browser_engine/script/event_loop_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: new event loop has zero pending rAF callbacks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/browser_engine/script/event_loop_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: schedule_raf increments pending rAF count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
