# math3d_spec

> Engine Math3D — Vec3, Mat4, Quaternion, Transform3D Tests

<!-- sdn-diagram:id=math3d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math3d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math3d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math3d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# math3d_spec

Engine Math3D — Vec3, Mat4, Quaternion, Transform3D Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/math3d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Math3D — Vec3, Mat4, Quaternion, Transform3D Tests

Tests 3D vector arithmetic, products, length, normalization,
matrix operations, quaternion rotation, and transform composition.

## Scenarios

### Vec3

### constructors

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

#### creates up vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3.up()
expect(v.x).to_equal(0.0)
expect(v.y).to_equal(1.0)
expect(v.z).to_equal(0.0)
```

</details>

### arithmetic

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
val a = Vec3(x: 5.0, y: 7.0, z: 9.0)
val b = Vec3(x: 2.0, y: 3.0, z: 4.0)
val c = a.sub(b)
expect(c.x).to_equal(3.0)
expect(c.y).to_equal(4.0)
expect(c.z).to_equal(5.0)
```

</details>

#### multiplies by scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3(x: 2.0, y: 3.0, z: 4.0)
val scaled = v.mul_scalar(2.0)
expect(scaled.x).to_equal(4.0)
expect(scaled.y).to_equal(6.0)
expect(scaled.z).to_equal(8.0)
```

</details>

### products

#### computes dot product

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(x: 1.0, y: 2.0, z: 3.0)
val b = Vec3(x: 4.0, y: 5.0, z: 6.0)
val d = a.dot(b)
expect(d).to_equal(32.0)
```

</details>

#### computes cross product

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(x: 1.0, y: 0.0, z: 0.0)
val b = Vec3(x: 0.0, y: 1.0, z: 0.0)
val c = a.cross(b)
expect(c.x).to_equal(0.0)
expect(c.y).to_equal(0.0)
expect(c.z).to_equal(1.0)
```

</details>

#### cross product of parallel vectors is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(x: 1.0, y: 0.0, z: 0.0)
val b = Vec3(x: 2.0, y: 0.0, z: 0.0)
val c = a.cross(b)
expect(c.x).to_equal(0.0)
expect(c.y).to_equal(0.0)
expect(c.z).to_equal(0.0)
```

</details>

### length and distance

#### computes length squared

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3(x: 1.0, y: 2.0, z: 2.0)
expect(v.length_squared()).to_equal(9.0)
```

</details>

#### computes length of (1,2,2) vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3(x: 1.0, y: 2.0, z: 2.0)
val len_i = v.length() * 1000.0
expect(len_i).to_be_greater_than(2999.0)
expect(len_i).to_be_less_than(3001.0)
```

</details>

#### normalizes a vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3(x: 0.0, y: 0.0, z: 5.0)
val n = v.normalize()
val nz_i = n.z * 1000.0
expect(nz_i).to_be_greater_than(999.0)
expect(nz_i).to_be_less_than(1001.0)
val nx_i = n.x * 1000.0
expect(nx_i).to_be_greater_than(-1.0)
expect(nx_i).to_be_less_than(1.0)
```

</details>

#### computes distance between two points

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(x: 0.0, y: 0.0, z: 0.0)
val b = Vec3(x: 1.0, y: 2.0, z: 2.0)
val dist_i = a.distance_to(b) * 1000.0
expect(dist_i).to_be_greater_than(2999.0)
expect(dist_i).to_be_less_than(3001.0)
```

</details>

### Mat4

<details>
<summary>Advanced: identity matrix has correct diagonal</summary>

#### identity matrix has correct diagonal

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mat4.identity()
expect(m.get(0, 0)).to_equal(1.0)
expect(m.get(1, 1)).to_equal(1.0)
expect(m.get(2, 2)).to_equal(1.0)
expect(m.get(3, 3)).to_equal(1.0)
expect(m.get(0, 1)).to_equal(0.0)
```

</details>


</details>

<details>
<summary>Advanced: translation matrix transforms point correctly</summary>

#### translation matrix transforms point correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Mat4.translation(10.0, 20.0, 30.0)
val p = Vec3.zero()
val result = t.transform_point(p)
expect(result.x).to_equal(10.0)
expect(result.y).to_equal(20.0)
expect(result.z).to_equal(30.0)
```

</details>


</details>

#### identity times identity is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Mat4.identity()
val b = Mat4.identity()
val c = a.mul(b)
expect(c.get(0, 0)).to_equal(1.0)
expect(c.get(1, 1)).to_equal(1.0)
expect(c.get(0, 1)).to_equal(0.0)
```

</details>

<details>
<summary>Advanced: scaling matrix scales point</summary>

#### scaling matrix scales point

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Mat4.scaling(2.0, 3.0, 4.0)
val p = Vec3(x: 1.0, y: 1.0, z: 1.0)
val result = s.transform_point(p)
expect(result.x).to_equal(2.0)
expect(result.y).to_equal(3.0)
expect(result.z).to_equal(4.0)
```

</details>


</details>

<details>
<summary>Advanced: perspective matrix produces non-zero values</summary>

#### perspective matrix produces non-zero values

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fov = Angle(radians: MATH_PI / 4.0)
val m = Mat4.perspective(fov, 1.5, 0.1, 100.0)
# Near plane mapped correctly — diagonal elements should be non-zero
val m00 = m.get(0, 0) * 1000.0
val m11 = m.get(1, 1) * 1000.0
expect(m00).to_be_greater_than(100.0)
expect(m11).to_be_greater_than(100.0)
```

</details>


</details>

### Quaternion

#### identity quaternion is (0,0,0,1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = Quaternion.identity()
expect(q.x).to_equal(0.0)
expect(q.y).to_equal(0.0)
expect(q.z).to_equal(0.0)
expect(q.w).to_equal(1.0)
```

</details>

#### from_axis_angle creates valid quaternion

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val axis = Vec3(x: 0.0, y: 1.0, z: 0.0)
val angle = Angle(radians: MATH_PI / 2.0)
val q = Quaternion.from_axis_angle(axis, angle)
# Length should be ~1.0
val len_i = q.length() * 1000.0
expect(len_i).to_be_greater_than(999.0)
expect(len_i).to_be_less_than(1001.0)
```

</details>

#### identity rotation preserves vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = Quaternion.identity()
val v = Vec3(x: 1.0, y: 2.0, z: 3.0)
val rotated = q.rotate_vector(v)
val dx = rotated.x * 1000.0
val dy = rotated.y * 1000.0
val dz = rotated.z * 1000.0
expect(dx).to_be_greater_than(999.0)
expect(dx).to_be_less_than(1001.0)
expect(dy).to_be_greater_than(1999.0)
expect(dy).to_be_less_than(2001.0)
expect(dz).to_be_greater_than(2999.0)
expect(dz).to_be_less_than(3001.0)
```

</details>

#### 90-degree Y rotation rotates X to Z

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val axis = Vec3(x: 0.0, y: 1.0, z: 0.0)
val angle = Angle(radians: MATH_PI / 2.0)
val q = Quaternion.from_axis_angle(axis, angle)
val v = Vec3(x: 1.0, y: 0.0, z: 0.0)
val rotated = q.rotate_vector(v)
# X-axis rotated 90 degrees around Y should become -Z
val rx_i = rotated.x * 1000.0
val rz_i = rotated.z * 1000.0
expect(rx_i).to_be_greater_than(-1.0)
expect(rx_i).to_be_less_than(1.0)
expect(rz_i).to_be_less_than(-999.0)
```

</details>

### Transform3D

#### identity transform preserves point

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform3D.identity()
val p = Vec3(x: 5.0, y: 10.0, z: 15.0)
val result = t.transform_point(p)
expect(result.x).to_equal(5.0)
expect(result.y).to_equal(10.0)
expect(result.z).to_equal(15.0)
```

</details>

#### composes two translations

1. position: Vec3
2. rotation: Quaternion identity
3. scale: Vec3 one
4. position: Vec3
5. rotation: Quaternion identity
6. scale: Vec3 one


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = Transform3D(
    position: Vec3(x: 100.0, y: 200.0, z: 300.0),
    rotation: Quaternion.identity(),
    scale: Vec3.one()
)
val child = Transform3D(
    position: Vec3(x: 10.0, y: 20.0, z: 30.0),
    rotation: Quaternion.identity(),
    scale: Vec3.one()
)
val composed = parent.compose(child)
val origin = Vec3.zero()
val result = composed.transform_point(origin)
val rx_i = result.x * 100.0
val ry_i = result.y * 100.0
val rz_i = result.z * 100.0
expect(rx_i).to_be_greater_than(10999.0)
expect(rx_i).to_be_less_than(11001.0)
expect(ry_i).to_be_greater_than(21999.0)
expect(ry_i).to_be_less_than(22001.0)
expect(rz_i).to_be_greater_than(32999.0)
expect(rz_i).to_be_less_than(33001.0)
```

</details>

#### forward returns correct direction

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform3D.identity()
val fwd = t.forward()
expect(fwd.z).to_equal(1.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
