# Frame Scheduler rAF Bounds Spec

> The scheduler is generic compositor infrastructure below browser-specific script execution. This spec proves rAF scheduling fails closed at the shared queue cap while preserving the queued callbacks already accepted.

<!-- sdn-diagram:id=frame_scheduler_raf_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=frame_scheduler_raf_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

frame_scheduler_raf_bounds_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=frame_scheduler_raf_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Frame Scheduler rAF Bounds Spec

The scheduler is generic compositor infrastructure below browser-specific script execution. This spec proves rAF scheduling fails closed at the shared queue cap while preserving the queued callbacks already accepted.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/web_rendering_backend_animation_hardening/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_async_mut/compositor/frame_scheduler_raf_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The scheduler is generic compositor infrastructure below browser-specific
script execution. This spec proves rAF scheduling fails closed at the shared
queue cap while preserving the queued callbacks already accepted.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** .spipe/web_rendering_backend_animation_hardening/state.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Syntax

The spec uses `std.spec` steps and direct value matchers. It fills the rAF
queue to the shared cap, submits one additional callback, then verifies the
pending and drained callback counts stay capped.

## Scenarios

### FrameScheduler requestAnimationFrame bounds

#### normalizes non-positive target fps before frame budget calculation

- Construct schedulers with invalid target frame rates
- Assert invalid rates are clamped before frame timing is calculated
   - Expected: zero_scheduler.target_fps equals `60`
   - Expected: negative_scheduler.target_fps equals `60`
   - Expected: zero_scheduler.frame_budget_ms equals `1000.0 / 60.0`
   - Expected: negative_scheduler.frame_budget_ms equals `1000.0 / 60.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Construct schedulers with invalid target frame rates")
val zero_scheduler = FrameScheduler.new(0)
val negative_scheduler = FrameScheduler.new(-30)

step("Assert invalid rates are clamped before frame timing is calculated")
expect(zero_scheduler.target_fps).to_equal(60)
expect(negative_scheduler.target_fps).to_equal(60)
expect(zero_scheduler.frame_budget_ms).to_equal(1000.0 / 60.0)
expect(negative_scheduler.frame_budget_ms).to_equal(1000.0 / 60.0)
```

</details>

#### caps excessive target fps before frame budget calculation

- Construct schedulers with high and excessive target frame rates
- Assert high refresh remains valid while pathological input is capped
   - Expected: high_scheduler.target_fps equals `144`
   - Expected: excessive_scheduler.target_fps equals `240`
   - Expected: excessive_scheduler.frame_budget_ms equals `1000.0 / 240.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Construct schedulers with high and excessive target frame rates")
val high_scheduler = FrameScheduler.new(144)
val excessive_scheduler = FrameScheduler.new(1000000)

step("Assert high refresh remains valid while pathological input is capped")
expect(high_scheduler.target_fps).to_equal(144)
expect(excessive_scheduler.target_fps).to_equal(240)
expect(excessive_scheduler.frame_budget_ms).to_equal(1000.0 / 240.0)
```

</details>

#### rejects negative frame timestamps before mutating scheduler state

- Construct a scheduler and submit a negative timestamp
- var scheduler = FrameScheduler new
- Assert no frame state was advanced from the invalid timestamp
   - Expected: scheduler.frame_count equals `0`
   - Expected: scheduler.first_frame_time equals `0.0`
   - Expected: scheduler.last_frame_time equals `0.0`
- Assert the next valid timestamp can still start the first frame
   - Expected: scheduler.frame_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Construct a scheduler and submit a negative timestamp")
var scheduler = FrameScheduler.new(60)
val accepted = scheduler.begin_frame(-1.0)

step("Assert no frame state was advanced from the invalid timestamp")
expect(accepted).to_be(false)
expect(scheduler.frame_count).to_equal(0)
expect(scheduler.first_frame_time).to_equal(0.0)
expect(scheduler.last_frame_time).to_equal(0.0)

step("Assert the next valid timestamp can still start the first frame")
expect(scheduler.begin_frame(0.0)).to_be(true)
expect(scheduler.frame_count).to_equal(1)
```

</details>

#### bounds remaining frame budget when timestamps are reversed

- Construct a scheduler and query reversed frame timing
- Assert remaining budget stays within the frame budget interval
   - Expected: scheduler.frame_budget_remaining(10.0, 0.0) equals `1000.0 / 60.0`
   - Expected: scheduler.frame_budget_remaining(0.0, 1.0) equals `(1000.0 / 60.0) - 1.0`
   - Expected: scheduler.frame_budget_remaining(0.0, 100.0) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Construct a scheduler and query reversed frame timing")
val scheduler = FrameScheduler.new(60)

step("Assert remaining budget stays within the frame budget interval")
expect(scheduler.frame_budget_remaining(10.0, 0.0)).to_equal(1000.0 / 60.0)
expect(scheduler.frame_budget_remaining(0.0, 1.0)).to_equal((1000.0 / 60.0) - 1.0)
expect(scheduler.frame_budget_remaining(0.0, 100.0)).to_equal(0.0)
```

</details>

#### caps dropped frame accounting for huge timestamp jumps

- Construct schedulers and start their first frame
- var normal scheduler = FrameScheduler new
- var huge jump scheduler = FrameScheduler new
- Advance one scheduler by a normal dropped-frame interval
   - Expected: normal_scheduler.dropped_frames equals `2`
- Advance the other scheduler by a pathological timestamp jump
   - Expected: huge_jump_scheduler.dropped_frames equals `240`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Construct schedulers and start their first frame")
var normal_scheduler = FrameScheduler.new(60)
var huge_jump_scheduler = FrameScheduler.new(60)
expect(normal_scheduler.begin_frame(0.0)).to_be(true)
expect(huge_jump_scheduler.begin_frame(0.0)).to_be(true)

step("Advance one scheduler by a normal dropped-frame interval")
expect(normal_scheduler.begin_frame(50.0)).to_be(true)
expect(normal_scheduler.dropped_frames).to_equal(2)

step("Advance the other scheduler by a pathological timestamp jump")
expect(huge_jump_scheduler.begin_frame(1000000000.0)).to_be(true)
expect(huge_jump_scheduler.dropped_frames).to_equal(240)
```

</details>

#### rejects negative animation callback ids before queue insertion

- Construct a scheduler and submit invalid and valid callback IDs
- var scheduler = FrameScheduler new
- scheduler request animation frame
- scheduler request animation frame
- Assert only the valid callback was queued
   - Expected: scheduler.pending_callback_count() equals `1`
   - Expected: callbacks.len().to_i64() equals `1`
   - Expected: callbacks[0] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Construct a scheduler and submit invalid and valid callback IDs")
var scheduler = FrameScheduler.new(60)
scheduler.request_animation_frame(-1)
scheduler.request_animation_frame(0)

step("Assert only the valid callback was queued")
expect(scheduler.pending_callback_count()).to_equal(1)
val callbacks = scheduler.take_callbacks()
expect(callbacks.len().to_i64()).to_equal(1)
expect(callbacks[0]).to_equal(0)
```

</details>

#### caps pending animation callbacks at the shared queue limit

- Fill the pending rAF queue to the shared cap
- var scheduler = FrameScheduler new
- scheduler request animation frame
- Submit one extra callback past the cap
- scheduler request animation frame
- Assert the pending queue did not grow past the cap
   - Expected: scheduler.pending_callback_count() equals `TEST_FRAME_SCHEDULER_MAX_PENDING_RAF`
   - Expected: callbacks.len().to_i64() equals `TEST_FRAME_SCHEDULER_MAX_PENDING_RAF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fill the pending rAF queue to the shared cap")
var scheduler = FrameScheduler.new(60)
var i = 0
while i < TEST_FRAME_SCHEDULER_MAX_PENDING_RAF:
    scheduler.request_animation_frame(i)
    i = i + 1

step("Submit one extra callback past the cap")
scheduler.request_animation_frame(999999)

step("Assert the pending queue did not grow past the cap")
expect(scheduler.pending_callback_count()).to_equal(TEST_FRAME_SCHEDULER_MAX_PENDING_RAF)
val callbacks = scheduler.take_callbacks()
expect(callbacks.len().to_i64()).to_equal(TEST_FRAME_SCHEDULER_MAX_PENDING_RAF)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [.spipe/web_rendering_backend_animation_hardening/state.md](.spipe/web_rendering_backend_animation_hardening/state.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
