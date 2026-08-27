# Quaternion Specification

> Quat (f32) and Quatd (f64) quaternion types for 3D rotations.

<!-- sdn-diagram:id=quat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=quat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

quat_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=quat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Quaternion Specification

Quat (f32) and Quatd (f64) quaternion types for 3D rotations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MATH-003 |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/quat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Quat (f32) and Quatd (f64) quaternion types for 3D rotations.

## Key Concepts
| Concept | Description |
|---------|-------------|
| Quat | Quaternion with f32 precision |
| SLERP | Spherical linear interpolation |
| Composition | Rotation composition via multiplication |

## Behavior
- Identity quaternion represents no rotation
- from_axis_angle and from_euler constructors
- SLERP interpolation for smooth rotation
- Quaternion-vector rotation

## Scenarios

### Quaternion Construction

#### creates identity quaternion

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = Quat.identity()
expect(q.w).to_equal(1.0)
expect(q.x).to_equal(0.0)
expect(q.y).to_equal(0.0)
expect(q.z).to_equal(0.0)
```

</details>

#### creates from axis-angle

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val axis = Vec3(x: 0.0, y: 1.0, z: 0.0)
val q = Quat.from_axis_angle(axis, 0.0)
# Zero rotation = identity
expect(q.w).to_equal(1.0)
```

</details>

#### normalizes a quaternion

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = Quat(w: 2.0, x: 0.0, y: 0.0, z: 0.0)
val n = q.normalize()
expect(n.w).to_equal(1.0)
expect(n.x).to_equal(0.0)
```

</details>

### Quaternion Rotation

#### identity rotation leaves vector unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = Quat.identity()
val v = Vec3(x: 1.0, y: 2.0, z: 3.0)
val r = q.rotate_vector(v)
expect(r.x).to_equal(1.0)
expect(r.y).to_equal(2.0)
expect(r.z).to_equal(3.0)
```

</details>

#### composes rotations via multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q1 = Quat.identity()
val q2 = Quat.identity()
val q3 = q1.mul(q2)
expect(q3.w).to_equal(1.0)
expect(q3.x).to_equal(0.0)
```

</details>

#### conjugate negates vector part

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = Quat(w: 1.0, x: 2.0, y: 3.0, z: 4.0)
val c = q.conjugate()
expect(c.w).to_equal(1.0)
expect(c.x).to_equal(-2.0)
expect(c.y).to_equal(-3.0)
expect(c.z).to_equal(-4.0)
```

</details>

### Quaternion SLERP

#### slerp at t=0 returns start

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Quat.identity()
val b = Quat.from_axis_angle(Vec3.up(), 1.57)
val r = a.slerp(b, 0.0)
# Should be close to a (floating-point tolerance)
var diff_w = r.w - a.w
if diff_w < 0.0:
    diff_w = 0.0 - diff_w
expect(diff_w < 0.1).to_equal(true)
```

</details>

#### slerp at t=1 returns end

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Quat.identity()
val axis = Vec3(x: 0.0, y: 1.0, z: 0.0)
val b = Quat.from_axis_angle(axis, 1.57)
val r = a.slerp(b, 1.0)
# Should be close to b (relaxed tolerance for interpreter precision)
var diff = r.w - b.w
if diff < 0.0:
    diff = 0.0 - diff
expect(diff < 0.1).to_equal(true)
```

</details>

### Quaternion Conversions

<details>
<summary>Advanced: converts to rotation matrix</summary>

#### converts to rotation matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = Quat.identity()
val m = q.to_mat4()
expect(m.data[0]).to_equal(1.0)
expect(m.data[5]).to_equal(1.0)
expect(m.data[10]).to_equal(1.0)
```

</details>


</details>

#### converts between f32 and f64

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q32 = Quat(w: 1.0, x: 0.0, y: 0.0, z: 0.0)
val q64 = q32.to_f64()
expect(q64.w).to_equal(1.0)
val q32b = q64.to_f32()
expect(q32b.w).to_equal(1.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
