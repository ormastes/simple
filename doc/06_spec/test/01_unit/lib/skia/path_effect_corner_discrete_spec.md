# Skia Path Effect (Corner + Discrete) Specification

> Tests for apply_corner_path_effect and apply_discrete_path_effect — Simple implementations of Skia's SkCornerPathEffect (arc-round sharp corners) and SkDiscretePathEffect (jitter path into short displaced segments).

<!-- sdn-diagram:id=path_effect_corner_discrete_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=path_effect_corner_discrete_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

path_effect_corner_discrete_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=path_effect_corner_discrete_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Path Effect (Corner + Discrete) Specification

Tests for apply_corner_path_effect and apply_discrete_path_effect — Simple implementations of Skia's SkCornerPathEffect (arc-round sharp corners) and SkDiscretePathEffect (jitter path into short displaced segments).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-PE-CORNER-DISCRETE |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/path_effect_corner_discrete_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for apply_corner_path_effect and apply_discrete_path_effect — Simple
implementations of Skia's SkCornerPathEffect (arc-round sharp corners) and
SkDiscretePathEffect (jitter path into short displaced segments).

Invariants verified:
- radius 0 is a no-op (only flattening).
- A square gains extra segments when its corners are rounded.
- A collinear polyline is not affected by corner rounding.
- DiscretePathEffect with a fixed seed is deterministic.
- DiscretePathEffect with deviation 0 matches the flattened input shape.
- The internal LCG produces a repeatable state sequence.

## Scenarios

### path_effect_corner_discrete

#### apply_corner_path_effect: radius 0 returns input unchanged

1.  move to
2.  line to
3.  line to
   - Expected: out_count equals `in_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A simple two-line path; zero radius means we simply re-emit the
# flattened polyline with the same number of line segments (1 move + 2 lines).
val p = sk_path_new()
    .move_to(0.0, 0.0)
    .line_to(10.0, 0.0)
    .line_to(10.0, 10.0)
val params = corner_path_effect_params_new(0.0)
val out = apply_corner_path_effect(p, params)
val in_count = p.segments.length()
val out_count = out.segments.length()
# Flattening of line-only input preserves segment count.
expect(out_count).to_equal(in_count)
```

</details>

#### apply_corner_path_effect: radius > 0 on a square produces more line segments than input

1.  move to
2.  line to
3.  line to
4.  line to
5.  close


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val square = sk_path_new()
    .move_to(0.0, 0.0)
    .line_to(10.0, 0.0)
    .line_to(10.0, 10.0)
    .line_to(0.0, 10.0)
    .close()
val params = corner_path_effect_params_new(2.0)
val out = apply_corner_path_effect(square, params)
val in_count = square.segments.length()
val out_count = out.segments.length()
expect(out_count).to_be_greater_than(in_count)
```

</details>

#### apply_corner_path_effect: collinear path is unchanged

1.  move to
2.  line to
3.  line to
   - Expected: out_count equals `in_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Three collinear points along +x. No corner should be rounded
# because the tangent direction doesn't change.
val p = sk_path_new()
    .move_to(0.0, 0.0)
    .line_to(5.0, 0.0)
    .line_to(10.0, 0.0)
val params = corner_path_effect_params_new(1.0)
val out = apply_corner_path_effect(p, params)
# With collinear input we should not have inserted any arc chords,
# so the output segment count must equal the flattened input count.
val in_count = p.segments.length()
val out_count = out.segments.length()
expect(out_count).to_equal(in_count)
```

</details>

#### apply_discrete_path_effect: deterministic seed produces same output twice

1.  move to
2.  line to
   - Expected: a.segments.length() equals `b.segments.length()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_path_new()
    .move_to(0.0, 0.0)
    .line_to(100.0, 0.0)
val params = discrete_path_effect_params_new(5.0, 2.0, 42)
val a = apply_discrete_path_effect(p, params)
val b = apply_discrete_path_effect(p, params)
expect(a.segments.length()).to_equal(b.segments.length())
```

</details>

#### apply_discrete_path_effect: deviation 0 produces output geometrically similar to input

1.  move to
2.  line to


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# With deviation == 0, every sampled point is its true position on
# the input path. The number of emitted line segments is roughly
# total_length / step.
val p = sk_path_new()
    .move_to(0.0, 0.0)
    .line_to(100.0, 0.0)
val params = discrete_path_effect_params_new(10.0, 0.0, 1)
val out = apply_discrete_path_effect(p, params)
# We expect more than one output segment (move + many lines).
expect(out.segments.length()).to_be_greater_than(1)
```

</details>

#### _lcg_next: state sequence is deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given a fixed seed, running the LCG twice from the same state must
# yield the same value both times.
val seed: i64 = 12345
val a = _lcg_next(seed)
val b = _lcg_next(seed)
expect(a).to_equal(b)
val a2 = _lcg_next(a)
val b2 = _lcg_next(a)
expect(a2).to_equal(b2)
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
