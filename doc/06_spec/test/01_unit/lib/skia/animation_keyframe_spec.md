# Skia Animation Keyframe Specification

> Tests for the keyframe sequencer — mirrors gfx::KeyframeModel and CSS @keyframes. Verifies construction, ordering, and sampling semantics (linear-interpolation at midpoints, clamping at endpoints, empty/duration edge cases).

<!-- sdn-diagram:id=animation_keyframe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=animation_keyframe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

animation_keyframe_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=animation_keyframe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Animation Keyframe Specification

Tests for the keyframe sequencer — mirrors gfx::KeyframeModel and CSS @keyframes. Verifies construction, ordering, and sampling semantics (linear-interpolation at midpoints, clamping at endpoints, empty/duration edge cases).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-ANI-002 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/animation_keyframe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the keyframe sequencer — mirrors gfx::KeyframeModel and CSS
@keyframes. Verifies construction, ordering, and sampling semantics
(linear-interpolation at midpoints, clamping at endpoints, empty/duration
edge cases).

## Scenarios

### animation_keyframe

#### keyframe_sequence_new: empty, count 0, sample returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = keyframe_sequence_new(1000.0)
val count = seq.keyframe_count()
val sampled = seq.sample(500.0)
val count_ok = count == 0
val sample_ok = math_abs(sampled - 0.0) < 1e-9
expect(count_ok).to_equal(true)
expect(sample_ok).to_equal(true)
```

</details>

#### add_keyframe: count increments

1. seq add keyframe
2. seq add keyframe
   - Expected: count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = keyframe_sequence_new(1.0)
val custom = ease_linear()
seq.add_keyframe(keyframe_new(0.0, 10.0, EasingKind.Linear, custom))
seq.add_keyframe(keyframe_new(1.0, 20.0, EasingKind.Linear, custom))
val count = seq.keyframe_count()
expect(count).to_equal(2)
```

</details>

#### add_keyframe: sorts by offset (add 0.5, then 0.2, sample agrees with sorted)

1. seq add keyframe
2. seq add keyframe
3. seq add keyframe
4. seq add keyframe
   - Expected: ok is true
   - Expected: count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = keyframe_sequence_new(1.0)
val custom = ease_linear()
seq.add_keyframe(keyframe_new(0.0, 0.0, EasingKind.Linear, custom))
seq.add_keyframe(keyframe_new(0.5, 50.0, EasingKind.Linear, custom))
seq.add_keyframe(keyframe_new(0.2, 20.0, EasingKind.Linear, custom))
seq.add_keyframe(keyframe_new(1.0, 100.0, EasingKind.Linear, custom))
# After sort, offsets should be 0.0, 0.2, 0.5, 1.0.
# Sample at 0.2 should give exactly 20.0 (the inserted keyframe value).
val sampled = seq.sample(0.2)
val ok = math_abs(sampled - 20.0) < 1e-9
expect(ok).to_equal(true)
val count = seq.keyframe_count()
expect(count).to_equal(4)
```

</details>

#### sample: at offset 0 returns first keyframe value

1. seq add keyframe
2. seq add keyframe
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = keyframe_sequence_new(1.0)
val custom = ease_linear()
seq.add_keyframe(keyframe_new(0.0, 7.5, EasingKind.Linear, custom))
seq.add_keyframe(keyframe_new(1.0, 99.0, EasingKind.Linear, custom))
val sampled = seq.sample(0.0)
val ok = math_abs(sampled - 7.5) < 1e-9
expect(ok).to_equal(true)
```

</details>

#### sample: at offset 1 returns last keyframe value

1. seq add keyframe
2. seq add keyframe
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = keyframe_sequence_new(1.0)
val custom = ease_linear()
seq.add_keyframe(keyframe_new(0.0, 7.5, EasingKind.Linear, custom))
seq.add_keyframe(keyframe_new(1.0, 99.0, EasingKind.Linear, custom))
val sampled = seq.sample(1.0)
val ok = math_abs(sampled - 99.0) < 1e-9
expect(ok).to_equal(true)
```

</details>

#### sample: at midpoint linearly interpolates when easing is Linear

1. seq add keyframe
2. seq add keyframe
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = keyframe_sequence_new(1.0)
val custom = ease_linear()
seq.add_keyframe(keyframe_new(0.0, 0.0, EasingKind.Linear, custom))
seq.add_keyframe(keyframe_new(1.0, 100.0, EasingKind.Linear, custom))
val sampled = seq.sample(0.5)
val ok = math_abs(sampled - 50.0) < 1e-9
expect(ok).to_equal(true)
expect(sampled).to_be_greater_than(49.0)
expect(sampled).to_be_less_than(51.0)
```

</details>

#### sample: duration 0 clamps to last keyframe

1. seq add keyframe
2. seq add keyframe
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seq = keyframe_sequence_new(0.0)
val custom = ease_linear()
seq.add_keyframe(keyframe_new(0.0, 0.0, EasingKind.Linear, custom))
seq.add_keyframe(keyframe_new(1.0, 42.0, EasingKind.Linear, custom))
val sampled = seq.sample(0.25)
val ok = math_abs(sampled - 42.0) < 1e-9
expect(ok).to_equal(true)
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


</details>
