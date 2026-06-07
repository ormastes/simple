# Skia Path Op Specification

> Tests for path_op(a, b, op) — the boolean polygon operations mirroring Skia's SkPathOps module (Union / Intersect / Difference / Xor).

<!-- sdn-diagram:id=path_op_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=path_op_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

path_op_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=path_op_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Path Op Specification

Tests for path_op(a, b, op) — the boolean polygon operations mirroring Skia's SkPathOps module (Union / Intersect / Difference / Xor).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-PATHOP |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/path_op_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for path_op(a, b, op) — the boolean polygon operations mirroring
Skia's SkPathOps module (Union / Intersect / Difference / Xor).

Tests use `SkPath.contains()` at representative points rather than asserting
exact vertex lists, which is robust against minor algorithm differences and
against the choice of EvenOdd vs Winding fill rule used internally.

## Scenarios

### path_op

#### Union of two overlapping rects produces a path whose bbox equals the outer union bbox

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A = [0,0,10,10], B = [5,5,15,15] — overlap [5,5,10,10],
# union bbox = [0,0,15,15].
val a = _make_rect(0.0, 0.0, 10.0, 10.0)
val b = _make_rect(5.0, 5.0, 15.0, 15.0)
val u = path_op(a, b, PathOp.Union)
val bb = u.bounds()
expect(bb.left).to_equal(0.0)
expect(bb.top).to_equal(0.0)
expect(bb.right).to_equal(15.0)
expect(bb.bottom).to_equal(15.0)
# Point in A-only region
expect(u.contains(2.0, 2.0)).to_equal(true)
# Point in B-only region
expect(u.contains(12.0, 12.0)).to_equal(true)
# Point in overlap
expect(u.contains(7.0, 7.0)).to_equal(true)
# Point outside both
expect(u.contains(20.0, 20.0)).to_equal(false)
```

</details>

#### Union of two disjoint rects produces a path containing both centers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A = [0,0,4,4] center (2,2), B = [10,10,14,14] center (12,12).
val a = _make_rect(0.0, 0.0, 4.0, 4.0)
val b = _make_rect(10.0, 10.0, 14.0, 14.0)
val u = path_op(a, b, PathOp.Union)
expect(u.contains(2.0, 2.0)).to_equal(true)
expect(u.contains(12.0, 12.0)).to_equal(true)
# Gap between them — should be outside.
expect(u.contains(7.0, 7.0)).to_equal(false)
```

</details>

#### Intersect of two overlapping rects contains only the overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A = [0,0,10,10], B = [5,5,15,15]; overlap = [5,5,10,10].
val a = _make_rect(0.0, 0.0, 10.0, 10.0)
val b = _make_rect(5.0, 5.0, 15.0, 15.0)
val i_path = path_op(a, b, PathOp.Intersect)
# Center of overlap region.
expect(i_path.contains(7.0, 7.0)).to_equal(true)
# A-only point — outside intersection.
expect(i_path.contains(2.0, 2.0)).to_equal(false)
# B-only point — outside intersection.
expect(i_path.contains(12.0, 12.0)).to_equal(false)
# Bbox should be the overlap rect.
val bb = i_path.bounds()
expect(bb.left).to_equal(5.0)
expect(bb.top).to_equal(5.0)
expect(bb.right).to_equal(10.0)
expect(bb.bottom).to_equal(10.0)
```

</details>

#### Intersect of two disjoint rects is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _make_rect(0.0, 0.0, 4.0, 4.0)
val b = _make_rect(10.0, 10.0, 14.0, 14.0)
val i_path = path_op(a, b, PathOp.Intersect)
# Neither rect's center lies in the intersection.
expect(i_path.contains(2.0, 2.0)).to_equal(false)
expect(i_path.contains(12.0, 12.0)).to_equal(false)
# Empty path has no segments (or only degenerate).
val seg_count = i_path.count_verbs()
val is_empty_ish = seg_count == 0
expect(is_empty_ish).to_equal(true)
```

</details>

#### Difference: rect minus centered smaller rect does NOT contain smaller rect center

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A = [0,0,10,10] (outer), B = [3,3,7,7] (inner, centered).
# A \ B should be the ring — center (5,5) is NOT in the result;
# points in the ring (e.g. (1,1)) ARE in the result.
val a = _make_rect(0.0, 0.0, 10.0, 10.0)
val b = _make_rect(3.0, 3.0, 7.0, 7.0)
val d = path_op(a, b, PathOp.Difference)
# Smaller rect center — carved out.
expect(d.contains(5.0, 5.0)).to_equal(false)
# Ring corner — still in A but not in B.
expect(d.contains(1.0, 1.0)).to_equal(true)
# Bbox should still be A's bbox (the ring spans all of A).
val bb = d.bounds()
val right_ok = bb.right >= 9.0
val bottom_ok = bb.bottom >= 9.0
expect(right_ok).to_equal(true)
expect(bottom_ok).to_equal(true)
```

</details>

#### Xor of two overlapping rects does NOT contain the overlap center

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A = [0,0,10,10], B = [5,5,15,15]; overlap center = (7.5, 7.5).
# Xor carves out the overlap; A-only and B-only regions remain.
val a = _make_rect(0.0, 0.0, 10.0, 10.0)
val b = _make_rect(5.0, 5.0, 15.0, 15.0)
val x = path_op(a, b, PathOp.Xor)
# Overlap center — carved out.
expect(x.contains(7.5, 7.5)).to_equal(false)
# A-only region — in xor.
expect(x.contains(2.0, 2.0)).to_equal(true)
# B-only region — in xor.
expect(x.contains(12.0, 12.0)).to_equal(true)
# Outside both — not in xor.
expect(x.contains(20.0, 20.0)).to_equal(false)
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
