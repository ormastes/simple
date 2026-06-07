# Skia Geometry Specification

> Tests for SkPoint, SkRect, SkSize, SkIRect, SkRRect geometry types.

<!-- sdn-diagram:id=geometry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=geometry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

geometry_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=geometry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Geometry Specification

Tests for SkPoint, SkRect, SkSize, SkIRect, SkRRect geometry types.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-002 |
| Category | Stdlib |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/geometry_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for SkPoint, SkRect, SkSize, SkIRect, SkRRect geometry types.

## Scenarios

### SkPoint

#### constructs with x and y

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_point(3.0, 4.0)
expect(p.x).to_equal(3.0)
expect(p.y).to_equal(4.0)
```

</details>

#### zero point has x=0 y=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_point_zero()
expect(p.x).to_equal(0.0)
expect(p.y).to_equal(0.0)
```

</details>

#### offset moves point

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_point(1.0, 2.0)
val q = p.offset(10.0, 20.0)
expect(q.x).to_equal(11.0)
expect(q.y).to_equal(22.0)
```

</details>

#### to_string contains coordinates

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = sk_point(1.0, 2.0)
val s = p.to_string()
expect(s).to_contain("SkPoint")
```

</details>

### SkSize

#### constructs with width and height

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = sk_size(100.0, 200.0)
expect(s.width).to_equal(100.0)
expect(s.height).to_equal(200.0)
```

</details>

#### is_empty true for zero size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = sk_size(0.0, 100.0)
expect(s.is_empty()).to_equal(true)
```

</details>

#### is_empty false for positive size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = sk_size(10.0, 10.0)
expect(s.is_empty()).to_equal(false)
```

</details>

#### is_empty true for negative width

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = sk_size(-1.0, 100.0)
expect(s.is_empty()).to_equal(true)
```

</details>

### SkISize

#### constructs with integer width and height

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = sk_isize(800, 600)
expect(s.width).to_equal(800)
expect(s.height).to_equal(600)
```

</details>

### SkRect

#### constructs from ltrb

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sk_rect(10.0, 20.0, 110.0, 70.0)
expect(r.left).to_equal(10.0)
expect(r.top).to_equal(20.0)
expect(r.right).to_equal(110.0)
expect(r.bottom).to_equal(70.0)
```

</details>

#### make_wh starts at origin

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sk_rect_make_wh(200.0, 100.0)
expect(r.left).to_equal(0.0)
expect(r.top).to_equal(0.0)
expect(r.right).to_equal(200.0)
expect(r.bottom).to_equal(100.0)
```

</details>

#### make_xywh sets position and size

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sk_rect_make_xywh(5.0, 10.0, 100.0, 50.0)
expect(r.left).to_equal(5.0)
expect(r.top).to_equal(10.0)
expect(r.right).to_equal(105.0)
expect(r.bottom).to_equal(60.0)
```

</details>

#### width() returns right - left

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sk_rect(10.0, 0.0, 90.0, 0.0)
expect(r.width()).to_equal(80.0)
```

</details>

#### height() returns bottom - top

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sk_rect(0.0, 5.0, 0.0, 55.0)
expect(r.height()).to_equal(50.0)
```

</details>

#### is_empty when left >= right

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sk_rect(50.0, 0.0, 50.0, 100.0)
expect(r.is_empty()).to_equal(true)
```

</details>

#### is_empty false for valid rect

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sk_rect_make_wh(100.0, 100.0)
expect(r.is_empty()).to_equal(false)
```

</details>

#### contains_point inside

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sk_rect(0.0, 0.0, 100.0, 100.0)
val p = SkPoint(x: 50.0, y: 50.0)
expect(r.contains_point(p)).to_equal(true)
```

</details>

#### contains_point outside

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sk_rect(0.0, 0.0, 100.0, 100.0)
val p = SkPoint(x: 150.0, y: 50.0)
expect(r.contains_point(p)).to_equal(false)
```

</details>

#### inset reduces rect

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sk_rect(0.0, 0.0, 100.0, 100.0)
val inset = r.inset(10.0, 10.0)
expect(inset.left).to_equal(10.0)
expect(inset.top).to_equal(10.0)
expect(inset.right).to_equal(90.0)
expect(inset.bottom).to_equal(90.0)
```

</details>

#### offset shifts rect

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sk_rect(10.0, 20.0, 110.0, 120.0)
val shifted = r.offset(5.0, -5.0)
expect(shifted.left).to_equal(15.0)
expect(shifted.top).to_equal(15.0)
```

</details>

#### intersects overlapping rects

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = sk_rect(0.0, 0.0, 100.0, 100.0)
val r2 = sk_rect(50.0, 50.0, 150.0, 150.0)
expect(r1.intersects(r2)).to_equal(true)
```

</details>

#### does not intersect disjoint rects

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = sk_rect(0.0, 0.0, 100.0, 100.0)
val r2 = sk_rect(200.0, 200.0, 300.0, 300.0)
expect(r1.intersects(r2)).to_equal(false)
```

</details>

### SkIRect

#### constructs from ltrb integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sk_irect(0, 0, 800, 600)
expect(r.width()).to_equal(800)
expect(r.height()).to_equal(600)
```

</details>

#### make_wh starts at origin

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sk_irect_make_wh(1920, 1080)
expect(r.left).to_equal(0)
expect(r.right).to_equal(1920)
```

</details>

#### is_empty when width is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sk_irect(10, 0, 10, 100)
expect(r.is_empty()).to_equal(true)
```

</details>

### SkRRect

#### constructs with rect and radii

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rect = sk_rect_make_wh(200.0, 100.0)
val rr = sk_rrect_make(rect, 10.0, 10.0)
expect(rr.radius_x).to_equal(10.0)
expect(rr.radius_y).to_equal(10.0)
```

</details>

#### is_rect when radii are zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rect = sk_rect_make_wh(100.0, 100.0)
val rr = sk_rrect_make(rect, 0.0, 0.0)
expect(rr.is_rect()).to_equal(true)
```

</details>

#### is_not_rect when radii are nonzero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rect = sk_rect_make_wh(100.0, 100.0)
val rr = sk_rrect_make(rect, 5.0, 5.0)
expect(rr.is_rect()).to_equal(false)
```

</details>

#### oval has radii equal to half size

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rect = sk_rect_make_wh(100.0, 60.0)
val rr = sk_rrect_make_oval(rect)
expect(rr.radius_x).to_equal(50.0)
expect(rr.radius_y).to_equal(30.0)
```

</details>

#### oval is_oval

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rect = sk_rect_make_wh(100.0, 60.0)
val rr = sk_rrect_make_oval(rect)
expect(rr.is_oval()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
