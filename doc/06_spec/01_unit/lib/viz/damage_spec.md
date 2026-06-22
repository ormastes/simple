# Damage Specification

> <details>

<!-- sdn-diagram:id=damage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=damage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

damage_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=damage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Damage Specification

## Scenarios

### damage

#### union_rects with empty second operand returns first

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _rect(10.0, 20.0, 50.0, 60.0)
val empty = _empty_rect()
val result = union_rects(a, empty)
val eq = _rect_eq(result, a)
eq.to_equal(true)
```

</details>

#### union_rects of two disjoint rects returns bounding box

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _rect(0.0, 0.0, 10.0, 10.0)
val b = _rect(20.0, 30.0, 40.0, 50.0)
val result = union_rects(a, b)
result.left.to_equal(0.0)
result.top.to_equal(0.0)
result.right.to_equal(40.0)
result.bottom.to_equal(50.0)
```

</details>

#### union_rects of two overlapping rects returns outer bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _rect(0.0, 0.0, 30.0, 30.0)
val b = _rect(20.0, 20.0, 50.0, 50.0)
val result = union_rects(a, b)
result.left.to_equal(0.0)
result.top.to_equal(0.0)
result.right.to_equal(50.0)
result.bottom.to_equal(50.0)
```

</details>

#### intersect_rect of disjoint rects returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _rect(0.0, 0.0, 10.0, 10.0)
val b = _rect(20.0, 20.0, 40.0, 40.0)
val result = intersect_rect(a, b)
result.left.to_equal(0.0)
result.top.to_equal(0.0)
result.right.to_equal(0.0)
result.bottom.to_equal(0.0)
```

</details>

#### intersect_rect of contained rects returns the smaller rect

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outer = _rect(0.0, 0.0, 100.0, 100.0)
val inner = _rect(10.0, 10.0, 40.0, 40.0)
val result = intersect_rect(outer, inner)
result.left.to_equal(10.0)
result.top.to_equal(10.0)
result.right.to_equal(40.0)
result.bottom.to_equal(40.0)
```

</details>

#### aggregate_damage with no children equals root damage clipped to viewport

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val viewport = _rect(0.0, 0.0, 800.0, 600.0)
val damage   = _rect(10.0, 20.0, 200.0, 150.0)
val root = _make_frame_with_damage(damage, viewport)
val no_children = [CompositorFrame]()
val no_clips    = [SkRect]()
val result = aggregate_damage(root, no_children, no_clips)
val eq = _rect_eq(result, damage)
eq.to_equal(true)
```

</details>

#### aggregate_damage unions child damage clipped by child clip rect

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val viewport      = _rect(0.0, 0.0, 800.0, 600.0)
val root_damage   = _rect(0.0, 0.0, 50.0, 50.0)
val root_frame    = _make_frame_with_damage(root_damage, viewport)

# child damage extends to (300, 300) but clip cuts it to (100, 100)
val child_damage  = _rect(0.0, 0.0, 300.0, 300.0)
val child_frame   = _make_frame_with_damage(child_damage, viewport)
val child_clip    = _rect(0.0, 0.0, 100.0, 100.0)

val children      = [child_frame]
val clips         = [child_clip]
val result        = aggregate_damage(root_frame, children, clips)

# union of root(0,0,50,50) and clipped-child(0,0,100,100) = (0,0,100,100)
# then clamped to viewport (0,0,800,600) => (0,0,100,100)
result.left.to_equal(0.0)
result.top.to_equal(0.0)
result.right.to_equal(100.0)
result.bottom.to_equal(100.0)
```

</details>

<details>
<summary>Advanced: propagate_damage_up through identity matrix returns unchanged rect</summary>

#### propagate_damage_up through identity matrix returns unchanged rect

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dmg    = _rect(10.0, 20.0, 80.0, 90.0)
val ident  = Matrix3x3.identity()
val result = propagate_damage_up(dmg, ident)
val eq = _rect_eq(result, dmg)
eq.to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/viz/damage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- damage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
