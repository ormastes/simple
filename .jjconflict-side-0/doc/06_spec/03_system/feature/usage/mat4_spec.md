# Mat4 Specification

> Mat4 (f32) and Mat4d (f64) 4x4 transformation matrices with column-major storage.

<!-- sdn-diagram:id=mat4_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mat4_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mat4_spec -> math
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mat4_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mat4 Specification

Mat4 (f32) and Mat4d (f64) 4x4 transformation matrices with column-major storage.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MATH-002 |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/mat4_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Mat4 (f32) and Mat4d (f64) 4x4 transformation matrices with column-major storage.

## Key Concepts
| Concept | Description |
|---------|-------------|
| Column-major | GPU/Vulkan standard storage order |
| Transform | Translation, rotation, scale factories |
| Projection | Perspective and orthographic projection |

## Behavior
- Column-major storage for GPU compatibility
- Factory methods for common transforms
- Matrix multiplication and inverse
- Point and vector transformation

## Scenarios

### Mat4 Identity and Factories

<details>
<summary>Advanced: creates identity matrix</summary>

#### creates identity matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = math.Mat4.identity()
expect m.data[0] == 1.0
expect m.data[5] == 1.0
expect m.data[10] == 1.0
expect m.data[15] == 1.0
expect m.data[1] == 0.0
```

</details>


</details>

<details>
<summary>Advanced: creates translation matrix</summary>

#### creates translation matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = math.Mat4.translation(1.0, 2.0, 3.0)
# Column-major: translation in column 3 (indices 12, 13, 14)
expect m.data[12] == 1.0
expect m.data[13] == 2.0
expect m.data[14] == 3.0
```

</details>


</details>

<details>
<summary>Advanced: creates scale matrix</summary>

#### creates scale matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = math.Mat4.scale(2.0, 3.0, 4.0)
expect m.data[0] == 2.0
expect m.data[5] == 3.0
expect m.data[10] == 4.0
```

</details>


</details>

### Mat4 Operations

#### multiplies identity by identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = math.Mat4.identity()
val b = math.Mat4.identity()
val c = a.mul(b)
expect c.data[0] == 1.0
expect c.data[5] == 1.0
expect c.data[10] == 1.0
expect c.data[15] == 1.0
```

</details>

#### multiplies translation matrices

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = math.Mat4.translation(1.0, 0.0, 0.0)
val b = math.Mat4.translation(0.0, 2.0, 0.0)
val c = a.mul(b)
# Combined translation: (1, 2, 0)
expect c.data[12] == 1.0
expect c.data[13] == 2.0
expect c.data[14] == 0.0
```

</details>

#### transforms a point

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = math.Mat4.translation(10.0, 20.0, 30.0)
val p = math.Vec3(1.0, 2.0, 3.0)
val result = m.transform_point(p)
expect result.x == 11.0
expect result.y == 22.0
expect result.z == 33.0
```

</details>

#### transforms a direction vector (ignores translation)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = math.Mat4.translation(10.0, 20.0, 30.0)
val v = math.Vec3(1.0, 0.0, 0.0)
val result = m.transform_vec3(v)
expect result.x == 1.0
expect result.y == 0.0
expect result.z == 0.0
```

</details>

<details>
<summary>Advanced: extracts 3x3 submatrix</summary>

#### extracts 3x3 submatrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = math.Mat4.scale(2.0, 3.0, 4.0)
val m3 = m.to_mat3()
expect m3.data[0] == 2.0
expect m3.data[4] == 3.0
expect m3.data[8] == 4.0
```

</details>


</details>

### Mat4 Inverse

#### inverts identity to identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = math.Mat4.identity()
val inv = m.inverse()
expect inv.data[0] == 1.0
expect inv.data[5] == 1.0
```

</details>

#### inverts translation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = math.Mat4.translation(5.0, 10.0, 15.0)
val inv = m.inverse()
# Inverse translation should negate
expect inv.data[12] == -5.0
expect inv.data[13] == -10.0
expect inv.data[14] == -15.0
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
