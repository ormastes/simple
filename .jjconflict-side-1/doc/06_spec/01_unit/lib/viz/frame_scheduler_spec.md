# Frame Scheduler Specification

> <details>

<!-- sdn-diagram:id=frame_scheduler_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=frame_scheduler_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

frame_scheduler_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=frame_scheduler_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Frame Scheduler Specification

## Scenarios

### frame_scheduler

#### frame_scheduler_new: state is Idle, missed_count is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = frame_scheduler_new(16.667)
s.missed_frames().to_equal(0)
match s.state:
    case FrameState.Idle:
        (true).to_equal(true)
    case _:
        (false).to_equal(true)
```

</details>

#### advance: first call emits FrameArgs

1. var s = frame scheduler new


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = frame_scheduler_new(16.667)
val maybe = s.advance(20.0)
match maybe:
    case Some(args):
        args.frame_id.to_equal(0)
        args.interval_ms.to_be_greater_than(16.0)
    case None:
        (false).to_equal(true)
```

</details>

#### advance: within interval returns None

1. var s = frame scheduler new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = frame_scheduler_new(16.667)
val first = s.advance(20.0)
val second = s.advance(25.0)
second.to_be_nil()
```

</details>

#### advance: after interval emits another FrameArgs with incremented frame_id

1. var s = frame scheduler new


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = frame_scheduler_new(16.667)
val first = s.advance(20.0)
val second = s.advance(40.0)
match second:
    case Some(args):
        args.frame_id.to_equal(1)
    case None:
        (false).to_equal(true)
```

</details>

#### target_fps: 16.667ms interval gives ~60 FPS

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = frame_scheduler_new(16.667)
val fps = s.target_fps()
fps.to_be_greater_than(59.0)
fps.to_be_less_than(61.0)
```

</details>

#### end_frame past deadline: increments missed_count

1. var s = frame scheduler new
2. s begin frame
3. s end frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = frame_scheduler_new(16.667)
val maybe = s.advance(20.0)
match maybe:
    case Some(args):
        s.begin_frame(args)
        s.end_frame(args.deadline + 5.0, args.deadline)
    case None:
        (false).to_equal(true)
s.missed_frames().to_equal(1)
```

</details>

#### reset: missed_count returns to 0

1. var s = frame scheduler new
2. s begin frame
3. s end frame
4. s reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = frame_scheduler_new(16.667)
val maybe = s.advance(20.0)
match maybe:
    case Some(args):
        s.begin_frame(args)
        s.end_frame(args.deadline + 5.0, args.deadline)
    case None:
        (false).to_equal(true)
s.missed_frames().to_equal(1)
s.reset()
s.missed_frames().to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/viz/frame_scheduler_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- frame_scheduler

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
