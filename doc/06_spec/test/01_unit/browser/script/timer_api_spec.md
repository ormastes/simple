# Timer API Spec

> Unit tests for the Simple browser engine Timer API.

<!-- sdn-diagram:id=timer_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=timer_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

timer_api_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=timer_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Timer API Spec

Unit tests for the Simple browser engine Timer API.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser/script/timer_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Unit tests for the Simple browser engine Timer API.

## Scenarios

### Timer API - setTimeout

#### schedules a one-shot timer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loop_ref = EventLoop.new()
val tid = set_timeout(loop_ref, 100, 1000)
expect(loop_ref.pending_timer_count()).to_equal(1)
```

</details>

#### returns a timer id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loop_ref = EventLoop.new()
val tid = set_timeout(loop_ref, 100, 500)
expect(tid > 0).to_equal(true)
```

</details>

#### assigns unique timer ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loop_ref = EventLoop.new()
val t1 = set_timeout(loop_ref, 100, 500)
val t2 = set_timeout(loop_ref, 101, 500)
expect(t1 != t2).to_equal(true)
```

</details>

### Timer API - setInterval

#### schedules a repeating timer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loop_ref = EventLoop.new()
val tid = set_interval(loop_ref, 200, 100)
expect(loop_ref.pending_timer_count()).to_equal(1)
```

</details>

### Timer API - clearTimeout

#### cancels a pending timeout

1. clear timeout
   - Expected: loop_ref.pending_timer_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loop_ref = EventLoop.new()
val tid = set_timeout(loop_ref, 100, 1000)
clear_timeout(loop_ref, tid)
expect(loop_ref.pending_timer_count()).to_equal(0)
```

</details>

### Timer API - clearInterval

#### cancels a pending interval

1. clear interval
   - Expected: loop_ref.pending_timer_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loop_ref = EventLoop.new()
val tid = set_interval(loop_ref, 200, 100)
clear_interval(loop_ref, tid)
expect(loop_ref.pending_timer_count()).to_equal(0)
```

</details>

### Timer API - requestAnimationFrame

#### registers a rAF callback

1. request animation frame
   - Expected: loop_ref.pending_raf_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loop_ref = EventLoop.new()
request_animation_frame(loop_ref, 300)
expect(loop_ref.pending_raf_count()).to_equal(1)
```

</details>

#### registers multiple rAF callbacks

1. request animation frame
2. request animation frame
   - Expected: loop_ref.pending_raf_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loop_ref = EventLoop.new()
request_animation_frame(loop_ref, 300)
request_animation_frame(loop_ref, 301)
expect(loop_ref.pending_raf_count()).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
