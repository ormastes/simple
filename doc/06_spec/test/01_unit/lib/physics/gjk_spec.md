# Gjk Specification

> 1. check

<!-- sdn-diagram:id=gjk_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gjk_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gjk_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gjk_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gjk Specification

## Scenarios

### GJK Collision Detection

#### detects sphere-sphere collision

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val detector = GJKCollisionDetector.new()
val s1 = Sphere.new(cx=0.0, cy=0.0, cz=0.0, r=1.0)
val s2 = Sphere.new(cx=1.5, cy=0.0, cz=0.0, r=1.0)
check(detector.detect_sphere_sphere(s1=s1, s2=s2) == true)
```

</details>

#### detects box-box collision

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val detector = GJKCollisionDetector.new()
val b1 = Box.new(cx=0.0, cy=0.0, cz=0.0, w=2.0, h=2.0, d=2.0)
val b2 = Box.new(cx=1.5, cy=0.0, cz=0.0, w=2.0, h=2.0, d=2.0)
check(detector.detect_box_box(b1=b1, b2=b2) == true)
```

</details>

#### detects convex hull collision

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val detector = GJKCollisionDetector.new()
val s = Sphere.new(cx=0.0, cy=0.0, cz=0.0, r=1.0)
val b = Box.new(cx=1.5, cy=0.0, cz=0.0, w=2.0, h=2.0, d=2.0)
check(detector.detect_convex_collision(s1=s, b1=b) == true)
```

</details>

#### handles non-colliding shapes

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val detector = GJKCollisionDetector.new()
val s1 = Sphere.new(cx=0.0, cy=0.0, cz=0.0, r=1.0)
val s2 = Sphere.new(cx=10.0, cy=10.0, cz=10.0, r=1.0)
check(detector.detect_sphere_sphere(s1=s1, s2=s2) == false)
```

</details>

#### calculates penetration depth

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val detector = GJKCollisionDetector.new()
val s1 = Sphere.new(cx=0.0, cy=0.0, cz=0.0, r=1.0)
val s2 = Sphere.new(cx=1.0, cy=0.0, cz=0.0, r=1.0)
val penetration = detector.calculate_penetration(s1=s1, s2=s2)
check(penetration > 0.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/physics/gjk_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GJK Collision Detection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
