# frustum_spec

> Engine Render Frustum — 2D frustum culling tests

<!-- sdn-diagram:id=frustum_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=frustum_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

frustum_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=frustum_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# frustum_spec

Engine Render Frustum — 2D frustum culling tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/frustum_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Render Frustum — 2D frustum culling tests

Tests frustum creation, point containment, AABB intersection,
circle intersection, and FrustumCuller batch operations.

## Scenarios

### Frustum2D

#### from_camera creates correct bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Frustum2D.from_camera(400.0, 300.0, 400.0, 300.0)
expect(f.min_x).to_be_greater_than(-0.01)
expect(f.min_x).to_be_less_than(0.01)
expect(f.min_y).to_be_greater_than(-0.01)
expect(f.min_y).to_be_less_than(0.01)
expect(f.max_x).to_be_greater_than(799.99)
expect(f.max_x).to_be_less_than(800.01)
expect(f.max_y).to_be_greater_than(599.99)
expect(f.max_y).to_be_less_than(600.01)
```

</details>

#### width and height are correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Frustum2D.from_camera(0.0, 0.0, 50.0, 30.0)
val w = f.width()
val h = f.height()
expect(w).to_be_greater_than(99.99)
expect(w).to_be_less_than(100.01)
expect(h).to_be_greater_than(59.99)
expect(h).to_be_less_than(60.01)
```

</details>

#### contains_point inside

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Frustum2D.from_camera(0.0, 0.0, 10.0, 10.0)
expect(f.contains_point(0.0, 0.0)).to_equal(true)
expect(f.contains_point(5.0, 5.0)).to_equal(true)
expect(f.contains_point(-5.0, -5.0)).to_equal(true)
```

</details>

#### contains_point outside

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Frustum2D.from_camera(0.0, 0.0, 10.0, 10.0)
expect(f.contains_point(15.0, 0.0)).to_equal(false)
expect(f.contains_point(0.0, 15.0)).to_equal(false)
```

</details>

#### intersects_aabb overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Frustum2D.from_camera(0.0, 0.0, 10.0, 10.0)
# Overlapping box
expect(f.intersects_aabb(-5.0, -5.0, 5.0, 5.0)).to_equal(true)
# Box fully inside
expect(f.intersects_aabb(-2.0, -2.0, 2.0, 2.0)).to_equal(true)
```

</details>

#### intersects_aabb no overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Frustum2D.from_camera(0.0, 0.0, 10.0, 10.0)
# Box far away
expect(f.intersects_aabb(20.0, 20.0, 30.0, 30.0)).to_equal(false)
```

</details>

#### intersects_circle overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Frustum2D.from_camera(0.0, 0.0, 10.0, 10.0)
# Circle at center
expect(f.intersects_circle(0.0, 0.0, 5.0)).to_equal(true)
# Circle touching edge
expect(f.intersects_circle(12.0, 0.0, 3.0)).to_equal(true)
```

</details>

#### intersects_circle no overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Frustum2D.from_camera(0.0, 0.0, 10.0, 10.0)
# Circle far away
expect(f.intersects_circle(30.0, 30.0, 2.0)).to_equal(false)
```

</details>

### FrustumCuller

#### cull_aabb adds visible ids

1. var culler = FrustumCuller new
   - Expected: v1 is true
   - Expected: v2 is false
   - Expected: v3 is true
   - Expected: culler.visible_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Frustum2D.from_camera(0.0, 0.0, 100.0, 100.0)
var culler = FrustumCuller.new(f)
val v1 = culler.cull_aabb(1, -10.0, -10.0, 10.0, 10.0)
val v2 = culler.cull_aabb(2, 200.0, 200.0, 210.0, 210.0)
val v3 = culler.cull_aabb(3, -50.0, -50.0, -40.0, -40.0)
expect(v1).to_equal(true)
expect(v2).to_equal(false)
expect(v3).to_equal(true)
expect(culler.visible_count()).to_equal(2)
```

</details>

#### cull_circle tracks visible

1. var culler = FrustumCuller new
   - Expected: v1 is true
   - Expected: v2 is false
   - Expected: culler.visible_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Frustum2D.from_camera(0.0, 0.0, 100.0, 100.0)
var culler = FrustumCuller.new(f)
val v1 = culler.cull_circle(10, 0.0, 0.0, 5.0)
val v2 = culler.cull_circle(20, 500.0, 500.0, 5.0)
expect(v1).to_equal(true)
expect(v2).to_equal(false)
expect(culler.visible_count()).to_equal(1)
```

</details>

#### reset clears visible ids

1. var culler = FrustumCuller new
2. culler cull aabb
   - Expected: culler.visible_count() equals `1`
3. culler reset
   - Expected: culler.visible_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Frustum2D.from_camera(0.0, 0.0, 100.0, 100.0)
var culler = FrustumCuller.new(f)
culler.cull_aabb(1, -10.0, -10.0, 10.0, 10.0)
expect(culler.visible_count()).to_equal(1)
culler.reset()
expect(culler.visible_count()).to_equal(0)
```

</details>

#### get_visible_ids returns correct ids

1. var culler = FrustumCuller new
2. culler cull aabb
3. culler cull circle
   - Expected: ids.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Frustum2D.from_camera(0.0, 0.0, 100.0, 100.0)
var culler = FrustumCuller.new(f)
culler.cull_aabb(42, -10.0, -10.0, 10.0, 10.0)
culler.cull_circle(99, 50.0, 50.0, 5.0)
val ids = culler.get_visible_ids()
expect(ids.len()).to_equal(2)
```

</details>

#### set_frustum updates for new frame

1. var culler = FrustumCuller new
   - Expected: v1 is false
2. culler set frustum
3. culler reset
   - Expected: v2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f1 = Frustum2D.from_camera(0.0, 0.0, 10.0, 10.0)
var culler = FrustumCuller.new(f1)
# Point at (50, 50) is outside f1
val v1 = culler.cull_aabb(1, 49.0, 49.0, 51.0, 51.0)
expect(v1).to_equal(false)
# Move frustum to include (50, 50)
val f2 = Frustum2D.from_camera(50.0, 50.0, 10.0, 10.0)
culler.set_frustum(f2)
culler.reset()
val v2 = culler.cull_aabb(1, 49.0, 49.0, 51.0, 51.0)
expect(v2).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
