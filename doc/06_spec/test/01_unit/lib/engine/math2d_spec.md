# math2d_spec

> Engine Math2D — Vec2 and Transform2D Tests

<!-- sdn-diagram:id=math2d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math2d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math2d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math2d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# math2d_spec

Engine Math2D — Vec2 and Transform2D Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/math2d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Math2D — Vec2 and Transform2D Tests

Tests vector arithmetic, products, length, interpolation,
and transform operations.

## Scenarios

### Vec2

### constructors

#### creates zero vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec2.zero()
expect(v.x).to_equal(0.0)
expect(v.y).to_equal(0.0)
```

</details>

#### creates one vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec2.one()
expect(v.x).to_equal(1.0)
expect(v.y).to_equal(1.0)
```

</details>

### arithmetic

#### adds two vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec2(x: 1.0, y: 2.0)
val b = Vec2(x: 3.0, y: 4.0)
val c = a.add(b)
expect(c.x).to_equal(4.0)
expect(c.y).to_equal(6.0)
```

</details>

#### subtracts two vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec2(x: 5.0, y: 7.0)
val b = Vec2(x: 2.0, y: 3.0)
val c = a.sub(b)
expect(c.x).to_equal(3.0)
expect(c.y).to_equal(4.0)
```

</details>

#### multiplies by scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec2(x: 2.0, y: 3.0)
val scaled = v.mul_scalar(4.0)
expect(scaled.x).to_equal(8.0)
expect(scaled.y).to_equal(12.0)
```

</details>

### products

#### computes dot product

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec2(x: 1.0, y: 2.0)
val b = Vec2(x: 3.0, y: 4.0)
val d = a.dot(b)
expect(d).to_equal(11.0)
```

</details>

#### computes cross product

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec2(x: 1.0, y: 0.0)
val b = Vec2(x: 0.0, y: 1.0)
val c = a.cross(b)
expect(c).to_equal(1.0)
```

</details>

### length and distance

#### computes length squared

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec2(x: 3.0, y: 4.0)
expect(v.length_squared()).to_equal(25.0)
```

</details>

#### computes length of (3,4) vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec2(x: 3.0, y: 4.0)
# length should be 5.0, use i64 truncation for comparison
val len_i = v.length() * 1000.0
expect(len_i).to_be_greater_than(4999.0)
expect(len_i).to_be_less_than(5001.0)
```

</details>

#### normalizes a vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec2(x: 0.0, y: 5.0)
val n = v.normalize()
# normalized y should be 1.0
val ny_i = n.y * 1000.0
expect(ny_i).to_be_greater_than(999.0)
expect(ny_i).to_be_less_than(1001.0)
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
val a = Vec2(x: 0.0, y: 0.0)
val b = Vec2(x: 3.0, y: 4.0)
val dist_i = a.distance_to(b) * 1000.0
expect(dist_i).to_be_greater_than(4999.0)
expect(dist_i).to_be_less_than(5001.0)
```

</details>

### interpolation

#### lerps between two vectors at t=0.5

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec2(x: 0.0, y: 0.0)
val b = Vec2(x: 10.0, y: 20.0)
val mid = a.lerp(b, 0.5)
expect(mid.x).to_equal(5.0)
expect(mid.y).to_equal(10.0)
```

</details>

### Transform2D

#### creates identity transform

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform2D.identity()
expect(t.position.x).to_equal(0.0)
expect(t.position.y).to_equal(0.0)
expect(t.rotation.radians).to_equal(0.0)
expect(t.scale.x).to_equal(1.0)
expect(t.scale.y).to_equal(1.0)
```

</details>

#### transforms a point with translation only

1. position: Vec2
2. rotation: Angle
3. scale: Vec2 one
   - Expected: result.x equals `15.0`
   - Expected: result.y equals `23.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform2D(
    position: Vec2(x: 10.0, y: 20.0),
    rotation: Angle(radians: 0.0),
    scale: Vec2.one()
)
val p = Vec2(x: 5.0, y: 3.0)
val result = t.transform_point(p)
expect(result.x).to_equal(15.0)
expect(result.y).to_equal(23.0)
```

</details>

#### transforms a point with scale only

1. position: Vec2 zero
2. rotation: Angle
3. scale: Vec2
   - Expected: result.x equals `8.0`
   - Expected: result.y equals `15.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform2D(
    position: Vec2.zero(),
    rotation: Angle(radians: 0.0),
    scale: Vec2(x: 2.0, y: 3.0)
)
val p = Vec2(x: 4.0, y: 5.0)
val result = t.transform_point(p)
expect(result.x).to_equal(8.0)
expect(result.y).to_equal(15.0)
```

</details>

#### composes two transforms (parent translation + child translation)

1. position: Vec2
2. rotation: Angle
3. scale: Vec2 one
4. position: Vec2
5. rotation: Angle
6. scale: Vec2 one


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = Transform2D(
    position: Vec2(x: 100.0, y: 200.0),
    rotation: Angle(radians: 0.0),
    scale: Vec2.one()
)
val child = Transform2D(
    position: Vec2(x: 10.0, y: 20.0),
    rotation: Angle(radians: 0.0),
    scale: Vec2.one()
)
val composed = parent.compose(child)
val origin = Vec2.zero()
val result = composed.transform_point(origin)
# parent(child(0,0)) = parent(10,20) = (110,220)
val rx_i = result.x * 100.0
val ry_i = result.y * 100.0
expect(rx_i).to_be_greater_than(10999.0)
expect(rx_i).to_be_less_than(11001.0)
expect(ry_i).to_be_greater_than(21999.0)
expect(ry_i).to_be_less_than(22001.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
