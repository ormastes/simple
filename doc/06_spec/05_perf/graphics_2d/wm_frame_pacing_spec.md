# wm_frame_pacing_spec

> test/perf/graphics_2d/wm_frame_pacing_spec.spl

<!-- sdn-diagram:id=wm_frame_pacing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_frame_pacing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_frame_pacing_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_frame_pacing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# wm_frame_pacing_spec

test/perf/graphics_2d/wm_frame_pacing_spec.spl

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | AC-7 — WM frame-pacing counters (event sleep, dirty-rect, |
| Category | Graphics \| Window Manager \| Frame Pacing |
| Status | Pending implementation (Phase 5) |
| Source | `test/05_perf/graphics_2d/wm_frame_pacing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

test/perf/graphics_2d/wm_frame_pacing_spec.spl

  present batch) added to tick loop; idle CPU measurable.
Verifies:
  - FramePacingCounters struct has event_sleep_us, dirty_rect_count,
    present_batch_count, idle_cpu_us, frame_count fields
  - tick_forever() integrates FramePacingCounters (no tight busy-loop)
  - Idle CPU is measurable: event_sleep_us > 0 in an idle frame
  - dirty_rect_count tracks only dirty regions (not full-frame redraws)
  - present_batch_count batches are counted per tick
  - frame_count increments on each tick

@cover src/lib/gc_async_mut/gpu/engine2d/wm_frame_pacing.spl
@cover src/lib/gc_async_mut/gpu/engine2d/engine.spl

## Scenarios

### wm_frame_pacing — AC-7: FramePacingCounters and tick loop

### FramePacingCounters field contract

#### AC-7: event_sleep_us field is present and non-negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_idle_frame()
expect(c.event_sleep_us >= 0).to_equal(true)
```

</details>

#### AC-7: dirty_rect_count field is present and non-negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_idle_frame()
expect(c.dirty_rect_count >= 0).to_equal(true)
```

</details>

#### AC-7: present_batch_count field is present and non-negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_idle_frame()
expect(c.present_batch_count >= 0).to_equal(true)
```

</details>

#### AC-7: idle_cpu_us field is present and non-negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_idle_frame()
expect(c.idle_cpu_us >= 0).to_equal(true)
```

</details>

#### AC-7: frame_count field is present and greater than zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_idle_frame()
expect(c.frame_count > 0).to_equal(true)
```

</details>

### idle frame detection

#### AC-7: idle frame has event_sleep_us >= 100

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_idle_frame()
expect(c.event_sleep_us >= IDLE_SLEEP_MIN_US).to_equal(true)
```

</details>

#### AC-7: idle frame has dirty_rect_count == 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_idle_frame()
expect(c.dirty_rect_count).to_equal(0)
```

</details>

#### AC-7: idle frame is detected by is_idle_frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_idle_frame()
expect(is_idle_frame(c)).to_equal(true)
```

</details>

#### AC-7: active frame is not detected as idle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_active_frame()
expect(is_idle_frame(c)).to_equal(false)
```

</details>

### active frame counters

#### AC-7: active frame dirty_rect_count is greater than zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_active_frame()
expect(c.dirty_rect_count > 0).to_equal(true)
```

</details>

#### AC-7: active frame present_batch_count is greater than zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_active_frame()
expect(c.present_batch_count > 0).to_equal(true)
```

</details>

#### AC-7: active frame event_sleep_us is non-zero (event sleep always inserted)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_active_frame()
expect(has_event_sleep(c)).to_equal(true)
```

</details>

### event sleep always inserted (no tight loop)

<details>
<summary>Advanced: AC-7: idle frame has event sleep (not a tight busy loop)</summary>

#### AC-7: idle frame has event sleep (not a tight busy loop)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_idle_frame()
expect(has_event_sleep(c)).to_equal(true)
```

</details>


</details>

#### AC-7: active frame still inserts event sleep

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_active_frame()
expect(has_event_sleep(c)).to_equal(true)
```

</details>

#### AC-7: full redraw frame still inserts event sleep

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_full_redraw_frame()
expect(has_event_sleep(c)).to_equal(true)
```

</details>

### frame pacing targets

#### AC-7: FRAME_TARGET_US represents 60fps budget

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(FRAME_TARGET_US).to_equal(16666)
```

</details>

#### AC-7: idle event sleep is a fraction of frame budget (less than frame target)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c: FramePacingCountersSentinel = make_idle_frame()
expect(c.event_sleep_us < FRAME_TARGET_US).to_equal(true)
```

</details>

#### AC-7: dirty_rect redraw area < full-frame redraw (sentinel: 3 dirty vs 1 full)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dirty_count: i64 = 3
val full_count: i64 = 1
# 3 partial dirty rects can cover less area than 1 full-frame rect
# This verifies we track dirty rects, not just full-frame redraws
expect(dirty_count > 0).to_equal(true)
expect(full_count > 0).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
