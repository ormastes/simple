# Skia Stroke Expansion Specification

> Tests for expand_stroke — the stroke-to-fill expansion helper mirroring Skia's SkStroke::strokePath. Given a stroked path plus width + cap + join, produces a closed fillable outline that, when filled, approximates the original stroked pixels.

<!-- sdn-diagram:id=stroke_expand_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stroke_expand_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stroke_expand_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stroke_expand_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Stroke Expansion Specification

Tests for expand_stroke — the stroke-to-fill expansion helper mirroring Skia's SkStroke::strokePath. Given a stroked path plus width + cap + join, produces a closed fillable outline that, when filled, approximates the original stroked pixels.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-STROKE-EXPAND |
| Category | Stdlib |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/stroke_expand_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for expand_stroke — the stroke-to-fill expansion helper mirroring
Skia's SkStroke::strokePath. Given a stroked path plus width + cap + join,
produces a closed fillable outline that, when filled, approximates the
original stroked pixels.

These tests avoid asserting exact vertex coordinates (which depend on the
join/cap polyline tessellation choices) and instead validate geometry via
SkPath.contains() point queries plus bounding-box comparisons.

## Scenarios

### stroke_expand

#### expand_stroke: width 0 produces empty-ish path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = sk_path_new().move_to(0.0, 0.0).line_to(10.0, 0.0)
val params = stroke_params_new(0.0, StrokeCap.Butt, StrokeJoin.Miter, 4.0)
val out = expand_stroke(input, params)
# Width <= 0 short-circuits to an empty path.
expect(out.is_empty()).to_equal(true)
```

</details>

#### expand_stroke: single horizontal line with Butt caps produces a rectangle

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Line from (0, 10) to (20, 10), width 4 -> expected filled rect (0,8,20,12).
val input = sk_path_new().move_to(0.0, 10.0).line_to(20.0, 10.0)
val params = stroke_params_new(4.0, StrokeCap.Butt, StrokeJoin.Miter, 4.0)
val out = expand_stroke(input, params)
# A point on the centerline must be inside.
expect(out.contains(10.0, 10.0)).to_equal(true)
# A point just outside the stroke band (y > 12) must be outside.
expect(out.contains(10.0, 20.0)).to_equal(false)
# A point well before the start cap (x < 0) must be outside.
expect(out.contains(-5.0, 10.0)).to_equal(false)
```

</details>

#### expand_stroke: right-angle L-shape with Miter join extends to the corner

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# L-shape: (0, 0) -> (10, 0) -> (10, 10), width 4.
# With a Miter join at (10, 0), the outside corner of the stroke
# should extend beyond the centerline corner into (12, -2) region.
val input = sk_path_new().move_to(0.0, 0.0).line_to(10.0, 0.0).line_to(10.0, 10.0)
val params = stroke_params_new(4.0, StrokeCap.Butt, StrokeJoin.Miter, 4.0)
val out = expand_stroke(input, params)
# The miter tip sits at roughly (12, -2).
val bounds = out.bounds()
# right edge should reach ~12 (stroke right side of vertical segment).
expect(bounds.right).to_be_greater_than(11.5)
```

</details>

#### expand_stroke: right-angle L-shape with Bevel join is shorter than Miter

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = sk_path_new().move_to(0.0, 0.0).line_to(10.0, 0.0).line_to(10.0, 10.0)
val miter_params = stroke_params_new(4.0, StrokeCap.Butt, StrokeJoin.Miter, 4.0)
val bevel_params = stroke_params_new(4.0, StrokeCap.Butt, StrokeJoin.Bevel, 4.0)
val miter_out = expand_stroke(input, miter_params)
val bevel_out = expand_stroke(input, bevel_params)
# The bevel outline's outer boundary is chamfered, so its outer corner
# does not reach as far as the miter tip. Verb count differs (bevel
# inserts one line_to for the chamfer; miter inserts two — miter tip + b).
val miter_verbs = miter_out.count_verbs()
val bevel_verbs = bevel_out.count_verbs()
expect(bevel_verbs).to_be_less_than(miter_verbs)
```

</details>

#### expand_stroke: closed square input produces a frame (outer + inner outlines)

1.  move to
2.  line to
3.  line to
4.  line to
5.  close
   - Expected: out contains `5.0, 0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Square (0,0)-(10,10), closed. Width 2.
# Expect an outer outline reaching ~(-1,-1)-(11,11) and an inner
# outline around (1,1)-(9,9). A point at the center (5,5) is NOT
# inside the stroke band (it's the interior hole); a point on an
# edge midline (5, 0) IS inside.
val input = sk_path_new()
    .move_to(0.0, 0.0)
    .line_to(10.0, 0.0)
    .line_to(10.0, 10.0)
    .line_to(0.0, 10.0)
    .close()
val params = stroke_params_new(2.0, StrokeCap.Butt, StrokeJoin.Miter, 4.0)
val out = expand_stroke(input, params)
# A point on the top edge centerline must be inside.
expect(out.contains(5.0, 0.0)).to_equal(true)
# The frame's outer bounds extend at least a half-width past the corner.
val bounds = out.bounds()
expect(bounds.right).to_be_greater_than(10.5)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
