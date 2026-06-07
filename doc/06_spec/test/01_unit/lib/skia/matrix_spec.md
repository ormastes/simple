# Skia Matrix Specification

> Tests for Matrix3x3 — identity, translate, scale, rotate, multiply.

<!-- sdn-diagram:id=matrix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=matrix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

matrix_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=matrix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Matrix Specification

Tests for Matrix3x3 — identity, translate, scale, rotate, multiply.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-003 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/matrix_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for Matrix3x3 — identity, translate, scale, rotate, multiply.

## Scenarios

### Matrix3x3 identity

#### is_identity returns true for identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Matrix3x3.identity()
expect(m.is_identity()).to_equal(true)
```

</details>

#### identity diagonal is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Matrix3x3.identity()
expect(m.m00).to_equal(1.0)
expect(m.m11).to_equal(1.0)
expect(m.m22).to_equal(1.0)
```

</details>

#### identity off-diagonal is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Matrix3x3.identity()
expect(m.m01).to_equal(0.0)
expect(m.m10).to_equal(0.0)
```

</details>

### Matrix3x3 translate

#### translate sets m02 and m12

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Matrix3x3.translate(10.0, 20.0)
expect(m.m02).to_equal(10.0)
expect(m.m12).to_equal(20.0)
```

</details>

#### translate keeps diagonal as 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Matrix3x3.translate(5.0, 15.0)
expect(m.m00).to_equal(1.0)
expect(m.m11).to_equal(1.0)
```

</details>

#### translate is not identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Matrix3x3.translate(1.0, 0.0)
expect(m.is_identity()).to_equal(false)
```

</details>

### Matrix3x3 scale

#### scale sets m00 and m11

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Matrix3x3.scale(2.0, 3.0)
expect(m.m00).to_equal(2.0)
expect(m.m11).to_equal(3.0)
```

</details>

#### scale sets m22 to 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Matrix3x3.scale(2.0, 3.0)
expect(m.m22).to_equal(1.0)
```

</details>

#### scale 1,1 is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Matrix3x3.scale(1.0, 1.0)
expect(m.is_identity()).to_equal(true)
```

</details>

### Matrix3x3 rotate

#### rotate 0 degrees is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Matrix3x3.rotate_degrees(0.0)
expect(m.is_identity()).to_equal(true)
```

</details>

#### rotate 90 degrees swaps sin/cos

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Matrix3x3.rotate_degrees(90.0)
# cos(90) ≈ 0, sin(90) ≈ 1
# m00 = cos = 0, m01 = -sin = -1, m10 = sin = 1, m11 = cos = 0
expect(m.m10).to_be_greater_than(0.99)
expect(m.m11).to_be_less_than(0.01)
```

</details>

#### rotate 180 degrees negates diagonal

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Matrix3x3.rotate_degrees(180.0)
# cos(180) ≈ -1
expect(m.m00).to_be_less_than(-0.99)
expect(m.m11).to_be_less_than(-0.99)
```

</details>

### Matrix3x3 multiply

#### identity times identity is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id = Matrix3x3.identity()
val result = id.mul(id)
expect(result.is_identity()).to_equal(true)
```

</details>

#### translate times translate accumulates

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t1 = Matrix3x3.translate(10.0, 0.0)
val t2 = Matrix3x3.translate(5.0, 0.0)
val result = t1.mul(t2)
expect(result.m02).to_equal(15.0)
```

</details>

#### scale times scale multiplies scales

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = Matrix3x3.scale(2.0, 3.0)
val s2 = Matrix3x3.scale(4.0, 2.0)
val result = s1.mul(s2)
expect(result.m00).to_equal(8.0)
expect(result.m11).to_equal(6.0)
```

</details>

### Matrix3x3 accessor decomposition

#### identity: tx=0, ty=0, scale_x=1, scale_y=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Matrix3x3.identity()
expect(m.tx()).to_equal(0.0)
expect(m.ty()).to_equal(0.0)
expect((m.scale_x() - 1.0).abs()).to_be_less_than(1e-6)
expect((m.scale_y() - 1.0).abs()).to_be_less_than(1e-6)
```

</details>

#### translate(5, 7): tx=5, ty=7, scale_x=1, scale_y=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Matrix3x3.translate(5.0, 7.0)
expect(m.tx()).to_equal(5.0)
expect(m.ty()).to_equal(7.0)
expect((m.scale_x() - 1.0).abs()).to_be_less_than(1e-6)
expect((m.scale_y() - 1.0).abs()).to_be_less_than(1e-6)
```

</details>

#### scale(2, 3): tx=0, ty=0, scale_x=2, scale_y=3

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Matrix3x3.scale(2.0, 3.0)
expect(m.tx()).to_equal(0.0)
expect(m.ty()).to_equal(0.0)
expect((m.scale_x() - 2.0).abs()).to_be_less_than(1e-6)
expect((m.scale_y() - 3.0).abs()).to_be_less_than(1e-6)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
