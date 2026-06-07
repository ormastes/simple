# Engine Core Facade Specification

> 1. var clock = Clock create

<!-- sdn-diagram:id=engine_core_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine_core_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine_core_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine_core_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Core Facade Specification

## Scenarios

### gc_async_mut engine core facade

#### re-exports clock, console, pool, and coroutine helpers

1. var clock = Clock create
2. clock tick
   - Expected: frame.frame_count equals `2`
3. var console = GameConsole new
4. console register command
   - Expected: console.has_command("ping") is true
5. var pool = ObjectPool new
   - Expected: pool.acquire("enemy") equals `0`
   - Expected: pool.count() equals `1`
6. var timer = WaitTimer wait seconds
   - Expected: timer.tick(0.6) is true
7. var frames = FrameCounter wait frames
   - Expected: frames.tick() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var clock = Clock.create(Seconds(value: 0.016))
clock.tick(1000000000)
val frame = clock.tick(1016000000)
expect(frame.frame_count).to_equal(2)
expect(frame.delta.value).to_be_greater_than(0.015)

var console = GameConsole.new(4)
console.register_command("ping", "Pong")
expect(console.has_command("ping")).to_equal(true)

var pool = ObjectPool.new(2)
expect(pool.acquire("enemy")).to_equal(0)
expect(pool.count()).to_equal(1)

var timer = WaitTimer.wait_seconds(0.5)
expect(timer.tick(0.6)).to_equal(true)
var frames = FrameCounter.wait_frames(1)
expect(frames.tick()).to_equal(true)
```

</details>

#### re-exports profiler records

1. var profiler = Profiler new
2. profiler begin scope
3. profiler end scope
   - Expected: profiler.sample_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = ProfileSample(name: "tick", start_ms: 1.0, end_ms: 4.0, depth: 0)
expect(sample.duration_ms()).to_equal(3.0)
var profiler = Profiler.new(8)
profiler.begin_scope("update", 0.0)
profiler.end_scope(2.0)
expect(profiler.sample_count()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/engine/core/engine_core_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut engine core facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
