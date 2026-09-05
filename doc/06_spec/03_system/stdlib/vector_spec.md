# Vector Specification

> <details>

<!-- sdn-diagram:id=vector_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vector_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vector_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vector_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vector Specification

## Scenarios

### SkPoint — zero

#### zero point has x equals 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = SkPoint.zero()
expect(p.x > -0.01).to_equal(true)
expect(p.x < 0.01).to_equal(true)
```

</details>

#### zero point has y equals 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = SkPoint.zero()
expect(p.y > -0.01).to_equal(true)
expect(p.y < 0.01).to_equal(true)
```

</details>

### SkPoint — distance_to

#### distance between known points

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = SkPoint(x: 0.0, y: 0.0)
val b = SkPoint(x: 3.0, y: 4.0)
val d = a.distance_to(b)
expect(d > 4.99).to_equal(true)
expect(d < 5.01).to_equal(true)
```

</details>

### SkRect — contains_point

#### inside point returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = SkRect.from_xywh(0.0, 0.0, 10.0, 10.0)
expect(r.contains_point(5.0, 5.0)).to_equal(true)
```

</details>

#### outside point returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = SkRect.from_xywh(0.0, 0.0, 10.0, 10.0)
expect(r.contains_point(15.0, 5.0)).to_equal(false)
```

</details>

### SkRect — center

#### center of rect is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = SkRect.from_xywh(0.0, 0.0, 10.0, 20.0)
val c = r.center()
expect(c.x > 4.99).to_equal(true)
expect(c.x < 5.01).to_equal(true)
expect(c.y > 9.99).to_equal(true)
expect(c.y < 10.01).to_equal(true)
```

</details>

### PathPoint — linear

#### linear point has_controls is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pos = SkPoint(x: 1.0, y: 2.0)
val pp = PathPoint.linear(pos)
expect(pp.has_controls).to_equal(false)
```

</details>

### Matrix3x3 — identity

#### identity diagonal is 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Matrix3x3.identity()
expect(m.m00 > 0.99).to_equal(true)
expect(m.m00 < 1.01).to_equal(true)
expect(m.m11 > 0.99).to_equal(true)
expect(m.m11 < 1.01).to_equal(true)
expect(m.m22 > 0.99).to_equal(true)
expect(m.m22 < 1.01).to_equal(true)
```

</details>

#### identity off-diagonal is 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Matrix3x3.identity()
expect(m.m01 > -0.01).to_equal(true)
expect(m.m01 < 0.01).to_equal(true)
expect(m.m10 > -0.01).to_equal(true)
expect(m.m10 < 0.01).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/stdlib/vector_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SkPoint — zero
- SkPoint — distance_to
- SkRect — contains_point
- SkRect — center
- PathPoint — linear
- Matrix3x3 — identity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
