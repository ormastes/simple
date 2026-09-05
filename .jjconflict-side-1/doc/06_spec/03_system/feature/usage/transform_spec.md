# Transform Specification

> Transform (f32) and Transformd (f64) combining position, rotation, and scale.

<!-- sdn-diagram:id=transform_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=transform_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

transform_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=transform_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Transform Specification

Transform (f32) and Transformd (f64) combining position, rotation, and scale.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MATH-004 |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/transform_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Transform (f32) and Transformd (f64) combining position, rotation, and scale.

## Key Concepts
| Concept | Description |
|---------|-------------|
| Transform | Position + rotation + scale |
| Composition | Parent-child transform combining |
| to_mat4 | Convert to 4x4 matrix |

## Behavior
- Identity transform: origin, no rotation, unit scale
- Compose transforms for hierarchy
- Convert to matrix for GPU upload
- SLERP-based interpolation

## Scenarios

### Transform Construction

#### creates identity transform

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform.identity()
expect(t.position.is_zero()).to_equal(true)
expect(t.rotation.w).to_equal(1.0)
expect(t.scale.x).to_equal(1.0)
expect(t.scale.y).to_equal(1.0)
expect(t.scale.z).to_equal(1.0)
```

</details>

#### converts to mat4

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform.identity()
val m = t.to_mat4()
expect(m.data[0]).to_equal(1.0)
expect(m.data[5]).to_equal(1.0)
expect(m.data[10]).to_equal(1.0)
expect(m.data[15]).to_equal(1.0)
```

</details>

### Transform Direction Vectors

#### identity forward is +Z

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform.identity()
val fwd = t.forward()
expect(fwd.z).to_equal(1.0)
```

</details>

#### identity right is +X

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform.identity()
val r = t.right()
expect(r.x).to_equal(1.0)
```

</details>

#### identity up is +Y

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform.identity()
val u = t.up()
expect(u.y).to_equal(1.0)
```

</details>

### Transform Composition

#### combines identity transforms

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = Transform.identity()
val child = Transform.identity()
val combined = parent.combine(child)
expect(combined.position.is_zero()).to_equal(true)
```

</details>

#### combines translation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = Transform(position: Vec3(x: 10.0, y: 0.0, z: 0.0), rotation: Quat.identity(), scale: Vec3.one())
val child = Transform(position: Vec3(x: 5.0, y: 0.0, z: 0.0), rotation: Quat.identity(), scale: Vec3.one())
val combined = parent.combine(child)
expect(combined.position.x).to_equal(15.0)
```

</details>

#### transforms a point

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform(position: Vec3(x: 10.0, y: 20.0, z: 30.0), rotation: Quat.identity(), scale: Vec3.one())
val p = Vec3(x: 1.0, y: 2.0, z: 3.0)
val result = t.transform_point(p)
expect(result.x).to_equal(11.0)
expect(result.y).to_equal(22.0)
expect(result.z).to_equal(33.0)
```

</details>

### Transform Interpolation

#### lerps between transforms

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Transform(position: Vec3.zero(), rotation: Quat.identity(), scale: Vec3.one())
val b = Transform(position: Vec3(x: 10.0, y: 10.0, z: 10.0), rotation: Quat.identity(), scale: Vec3.one())
val mid = a.lerp(b, 0.5)
expect(mid.position.x).to_equal(5.0)
expect(mid.position.y).to_equal(5.0)
expect(mid.position.z).to_equal(5.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
