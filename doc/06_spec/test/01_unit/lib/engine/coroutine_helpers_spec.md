# Coroutine Helpers Specification

> <details>

<!-- sdn-diagram:id=coroutine_helpers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=coroutine_helpers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

coroutine_helpers_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=coroutine_helpers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coroutine Helpers Specification

## Scenarios

### WaitTimer

#### creates a timer with duration

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timer = WaitTimer.wait_seconds(2.0)
expect(timer.is_done()).to_equal(false)
expect(timer.elapsed).to_equal(0.0)
expect(timer.duration).to_equal(2.0)
```

</details>

#### advances with tick and returns false before done

1. var timer = WaitTimer wait seconds
   - Expected: result is false
   - Expected: timer.elapsed equals `0.3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = WaitTimer.wait_seconds(1.0)
val result = timer.tick(0.3)
expect(result).to_equal(false)
expect(timer.elapsed).to_equal(0.3)
```

</details>

#### returns true when timer completes

1. var timer = WaitTimer wait seconds
2. timer tick
   - Expected: result is true
   - Expected: timer.is_done() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = WaitTimer.wait_seconds(0.5)
timer.tick(0.3)
val result = timer.tick(0.3)
expect(result).to_equal(true)
expect(timer.is_done()).to_equal(true)
```

</details>

#### clamps elapsed to duration

1. var timer = WaitTimer wait seconds
2. timer tick
   - Expected: timer.elapsed equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = WaitTimer.wait_seconds(1.0)
timer.tick(2.0)
expect(timer.elapsed).to_equal(1.0)
```

</details>

#### reports progress from 0 to 1

1. var timer = WaitTimer wait seconds
   - Expected: timer.progress() equals `0.0`
2. timer tick
   - Expected: timer.progress() equals `0.5`
3. timer tick
   - Expected: timer.progress() equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = WaitTimer.wait_seconds(2.0)
expect(timer.progress()).to_equal(0.0)
timer.tick(1.0)
expect(timer.progress()).to_equal(0.5)
timer.tick(1.0)
expect(timer.progress()).to_equal(1.0)
```

</details>

#### handles zero duration

1. var timer = WaitTimer wait seconds
   - Expected: timer.progress() equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = WaitTimer.wait_seconds(0.0)
expect(timer.progress()).to_equal(1.0)
```

</details>

#### stays done after completion

1. var timer = WaitTimer wait seconds
2. timer tick
   - Expected: result is true
   - Expected: timer.is_done() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = WaitTimer.wait_seconds(0.1)
timer.tick(0.2)
val result = timer.tick(0.1)
expect(result).to_equal(true)
expect(timer.is_done()).to_equal(true)
```

</details>

### FrameCounter

#### creates a counter with target frames

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val counter = FrameCounter.wait_frames(5)
expect(counter.is_done()).to_equal(false)
expect(counter.current).to_equal(0)
expect(counter.target).to_equal(5)
```

</details>

#### advances by one frame per tick

1. var counter = FrameCounter wait frames
   - Expected: r1 is false
   - Expected: counter.current equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var counter = FrameCounter.wait_frames(3)
val r1 = counter.tick()
expect(r1).to_equal(false)
expect(counter.current).to_equal(1)
```

</details>

#### returns true when target reached

1. var counter = FrameCounter wait frames
2. counter tick
   - Expected: result is true
   - Expected: counter.is_done() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var counter = FrameCounter.wait_frames(2)
counter.tick()
val result = counter.tick()
expect(result).to_equal(true)
expect(counter.is_done()).to_equal(true)
```

</details>

#### stays done after completion

1. var counter = FrameCounter wait frames
2. counter tick
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var counter = FrameCounter.wait_frames(1)
counter.tick()
val result = counter.tick()
expect(result).to_equal(true)
```

</details>

### ConditionWait

#### stores a condition function name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cw = ConditionWait(check_fn_name: "is_level_loaded", done: false)
expect(cw.check_fn_name).to_equal("is_level_loaded")
expect(cw.done).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/coroutine_helpers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WaitTimer
- FrameCounter
- ConditionWait

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
