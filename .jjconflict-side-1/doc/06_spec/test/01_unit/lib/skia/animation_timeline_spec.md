# Animation Timeline Specification

> Unit oracle for the tick-driven animation timeline: injected elapsed time maps to an eased value between two endpoints. Runs in the unit lane (expectation failures are not masked here) so it is the authoritative gate for the timeline used by the widget Draw-IR pipeline's progress/transition rendering.

<!-- sdn-diagram:id=animation_timeline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=animation_timeline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

animation_timeline_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=animation_timeline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Animation Timeline Specification

Unit oracle for the tick-driven animation timeline: injected elapsed time maps to an eased value between two endpoints. Runs in the unit lane (expectation failures are not masked here) so it is the authoritative gate for the timeline used by the widget Draw-IR pipeline's progress/transition rendering.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | W1d, G1.6 |
| Category | Stdlib \| Animation |
| Status | Active |
| Source | `test/01_unit/lib/skia/animation_timeline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit oracle for the tick-driven animation timeline: injected elapsed time maps
to an eased value between two endpoints. Runs in the unit lane (expectation
failures are not masked here) so it is the authoritative gate for the timeline
used by the widget Draw-IR pipeline's progress/transition rendering.

## Scenarios

### animation_timeline

#### linear timeline maps elapsed time directly to value

- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tl = timeline_new(0.0, 100.0, 100.0, EasingKind.Linear)
assert_true(math_abs(timeline_value_at(tl, 0.0) - 0.0) < 1e-9)
assert_true(math_abs(timeline_value_at(tl, 25.0) - 25.0) < 1e-9)
assert_true(math_abs(timeline_value_at(tl, 50.0) - 50.0) < 1e-9)
assert_true(math_abs(timeline_value_at(tl, 100.0) - 100.0) < 1e-9)
```

</details>

#### progress clamps to [0,1] and saturates past the duration

- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tl = timeline_new(0.0, 100.0, 100.0, EasingKind.Linear)
assert_true(math_abs(timeline_progress(tl, -10.0) - 0.0) < 1e-9)
assert_true(math_abs(timeline_progress(tl, 50.0) - 0.5) < 1e-9)
assert_true(math_abs(timeline_progress(tl, 250.0) - 1.0) < 1e-9)
assert_true(math_abs(timeline_value_at(tl, 250.0) - 100.0) < 1e-9)
```

</details>

#### zero-duration timeline resolves immediately to the end value

- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tl = timeline_new(0.0, 100.0, 0.0, EasingKind.Linear)
assert_true(math_abs(timeline_value_at(tl, 0.0) - 100.0) < 1e-9)
assert_true(timeline_done(tl, 0.0))
```

</details>

#### ease-in-out is symmetric at the midpoint and slow at the ends

- assert true
- assert true
- assert true
- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tl = timeline_new(0.0, 100.0, 100.0, EasingKind.EaseInOut)
val v25 = timeline_value_at(tl, 25.0)
val v40 = timeline_value_at(tl, 40.0)
val v50 = timeline_value_at(tl, 50.0)
val v60 = timeline_value_at(tl, 60.0)
val v75 = timeline_value_at(tl, 75.0)
# midpoint lands at 50 (symmetric curve)
assert_true(math_abs(v50 - 50.0) < 0.5)
# slow start / fast finish: below the diagonal before 50, above after
assert_true(v25 < 25.0)
assert_true(v40 < 40.0)
assert_true(v60 > 60.0)
assert_true(v75 > 75.0)
# the 40ms/60ms samples the widget spec renders land in fill-probe range
assert_true(v40 > 20.0)
assert_true(v60 < 80.0)
```

</details>

#### value is monotonically non-decreasing across ticks

- var prev = timeline value at
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tl = timeline_new(0.0, 100.0, 100.0, EasingKind.EaseInOut)
var prev = timeline_value_at(tl, 0.0)
var t = 10.0
while t <= 100.0:
    val cur = timeline_value_at(tl, t)
    assert_true(cur >= prev - 1e-9)
    prev = cur
    t = t + 10.0
```

</details>

#### endpoints and direction are honored (descending range)

- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tl = timeline_new(100.0, 0.0, 50.0, EasingKind.Linear)
assert_true(math_abs(timeline_value_at(tl, 0.0) - 100.0) < 1e-9)
assert_true(math_abs(timeline_value_at(tl, 25.0) - 50.0) < 1e-9)
assert_true(math_abs(timeline_value_at(tl, 50.0) - 0.0) < 1e-9)
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
