# Vec3 Specification

> Vec3 (f32) and Vec3d (f64) 3D vector types with arithmetic, geometric, and utility methods.

<!-- sdn-diagram:id=vec3_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vec3_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vec3_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vec3_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vec3 Specification

Vec3 (f32) and Vec3d (f64) 3D vector types with arithmetic, geometric, and utility methods.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MATH-001 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/vec3_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Vec3 (f32) and Vec3d (f64) 3D vector types with arithmetic, geometric, and utility methods.

## Key Concepts
| Concept | Description |
|---------|-------------|
| Vec3 | 3D vector with f32 precision |
| Vec3d | 3D vector with f64 precision |
| Dual precision | All types in both f32 and f64 |

## Behavior
- Supports add, sub, scale, dot, cross operations
- Magnitude/length aliases
- Static factory methods for common directions
- Conversion between f32 and f64

## Scenarios

### Vec3 Construction

#### creates a vector with components

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3(x: 1.0, y: 2.0, z: 3.0)
expect(v.x).to_equal(1.0)
expect(v.y).to_equal(2.0)
expect(v.z).to_equal(3.0)
```

</details>

#### creates zero vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3.zero()
expect(v.x).to_equal(0.0)
expect(v.y).to_equal(0.0)
expect(v.z).to_equal(0.0)
```

</details>

#### creates one vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3.one()
expect(v.x).to_equal(1.0)
expect(v.y).to_equal(1.0)
expect(v.z).to_equal(1.0)
```

</details>

#### creates directional vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Vec3.up().y).to_equal(1.0)
expect(Vec3.down().y).to_equal(-1.0)
expect(Vec3.left().x).to_equal(-1.0)
expect(Vec3.right().x).to_equal(1.0)
expect(Vec3.forward().z).to_equal(1.0)
expect(Vec3.back().z).to_equal(-1.0)
```

</details>

### Vec3 Arithmetic

#### adds two vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(x: 1.0, y: 2.0, z: 3.0)
val b = Vec3(x: 4.0, y: 5.0, z: 6.0)
val c = a.add(b)
expect(c.x).to_equal(5.0)
expect(c.y).to_equal(7.0)
expect(c.z).to_equal(9.0)
```

</details>

#### subtracts two vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(x: 4.0, y: 5.0, z: 6.0)
val b = Vec3(x: 1.0, y: 2.0, z: 3.0)
val c = a.sub(b)
expect(c.x).to_equal(3.0)
expect(c.y).to_equal(3.0)
expect(c.z).to_equal(3.0)
```

</details>

#### scales a vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3(x: 1.0, y: 2.0, z: 3.0)
val s = v.scale(2.0)
expect(s.x).to_equal(2.0)
expect(s.y).to_equal(4.0)
expect(s.z).to_equal(6.0)
```

</details>

#### computes dot product

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(x: 1.0, y: 0.0, z: 0.0)
val b = Vec3(x: 0.0, y: 1.0, z: 0.0)
expect(a.dot(b)).to_equal(0.0)

val c = Vec3(x: 1.0, y: 2.0, z: 3.0)
val d = Vec3(x: 4.0, y: 5.0, z: 6.0)
expect(c.dot(d)).to_equal(32.0)
```

</details>

#### computes cross product

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xv = Vec3(x: 1.0, y: 0.0, z: 0.0)
val yv = Vec3(x: 0.0, y: 1.0, z: 0.0)
val zv = xv.cross(yv)
expect(zv.x).to_equal(0.0)
expect(zv.y).to_equal(0.0)
expect(zv.z).to_equal(1.0)
```

</details>

### Vec3 Geometric Methods

#### computes magnitude

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3(x: 3.0, y: 4.0, z: 0.0)
expect(v.magnitude()).to_equal(5.0)
```

</details>

#### magnitude and length are aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3(x: 3.0, y: 4.0, z: 0.0)
expect(v.magnitude()).to_equal(v.length())
```

</details>

#### normalizes a vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3(x: 3.0, y: 0.0, z: 0.0)
val n = v.normalize()
expect(n.x).to_equal(1.0)
expect(n.y).to_equal(0.0)
expect(n.z).to_equal(0.0)
```

</details>

#### computes distance

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(x: 0.0, y: 0.0, z: 0.0)
val b = Vec3(x: 3.0, y: 4.0, z: 0.0)
expect(a.distance(b)).to_equal(5.0)
```

</details>

#### distance and distance_to are aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(x: 0.0, y: 0.0, z: 0.0)
val b = Vec3(x: 3.0, y: 4.0, z: 0.0)
expect(a.distance(b)).to_equal(a.distance_to(b))
```

</details>

#### interpolates linearly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(x: 0.0, y: 0.0, z: 0.0)
val b = Vec3(x: 10.0, y: 10.0, z: 10.0)
val mid = a.lerp(b, 0.5)
expect(mid.x).to_equal(5.0)
expect(mid.y).to_equal(5.0)
expect(mid.z).to_equal(5.0)
```

</details>

### Vec3 Utility Methods

#### detects zero vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Vec3.zero().is_zero()).to_equal(true)
expect(Vec3(x: 1.0, y: 0.0, z: 0.0).is_zero()).to_equal(false)
```

</details>

#### detects near-zero vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3(x: 0.0000001, y: 0.0, z: 0.0)
expect(v.is_near_zero()).to_equal(true)
```

</details>

#### checks unit vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Vec3(x: 1.0, y: 0.0, z: 0.0).is_unit()).to_equal(true)
expect(Vec3(x: 2.0, y: 0.0, z: 0.0).is_unit()).to_equal(false)
```

</details>

#### computes component min/max

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(x: 1.0, y: 5.0, z: 3.0)
val b = Vec3(x: 4.0, y: 2.0, z: 6.0)
val mn = a.component_min(b)
val mx = a.component_max(b)
expect(mn.x).to_equal(1.0)
expect(mn.y).to_equal(2.0)
expect(mn.z).to_equal(3.0)
expect(mx.x).to_equal(4.0)
expect(mx.y).to_equal(5.0)
expect(mx.z).to_equal(6.0)
```

</details>

### Vec3d and Conversions

#### creates Vec3d with f64 precision

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3d(x: 1.0, y: 2.0, z: 3.0)
expect(v.x).to_equal(1.0)
expect(v.y).to_equal(2.0)
expect(v.z).to_equal(3.0)
```

</details>

#### converts Vec3 to Vec3d

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v32 = Vec3(x: 1.0, y: 2.0, z: 3.0)
val v64 = v32.to_f64()
expect(v64.x).to_equal(1.0)
expect(v64.y).to_equal(2.0)
expect(v64.z).to_equal(3.0)
```

</details>

#### converts Vec3d to Vec3

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v64 = Vec3d(x: 1.0, y: 2.0, z: 3.0)
val v32 = v64.to_f32()
expect(v32.x).to_equal(1.0)
expect(v32.y).to_equal(2.0)
expect(v32.z).to_equal(3.0)
```

</details>

#### Vec3d has all Vec3 methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3d(x: 1.0, y: 2.0, z: 3.0)
val b = Vec3d(x: 4.0, y: 5.0, z: 6.0)
expect(a.dot(b)).to_equal(32.0)
val c = a.cross(b)
expect(c.x).to_equal(-3.0)
expect(c.y).to_equal(6.0)
expect(c.z).to_equal(-3.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
