# Math Specification

> <details>

<!-- sdn-diagram:id=math_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 168 | 168 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Specification

## Scenarios

### Vec2

#### constructors

#### zero returns (0, 0)

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

#### one returns (1, 1)

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

#### constructs with given values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec2(3.0, 4.0)
expect(v.x).to_equal(3.0)
expect(v.y).to_equal(4.0)
```

</details>

#### arithmetic

#### adds two vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec2(1.0, 2.0)
val b = Vec2(3.0, 4.0)
val r = a.add(b)
expect(r.x).to_equal(4.0)
expect(r.y).to_equal(6.0)
```

</details>

#### subtracts two vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec2(5.0, 7.0)
val b = Vec2(2.0, 3.0)
val r = a.sub(b)
expect(r.x).to_equal(3.0)
expect(r.y).to_equal(4.0)
```

</details>

#### scales by scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec2(2.0, 3.0)
val r = v.scale(2.0)
expect(r.x).to_equal(4.0)
expect(r.y).to_equal(6.0)
```

</details>

#### scales by zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec2(2.0, 3.0)
val r = v.scale(0.0)
expect(r.x).to_equal(0.0)
expect(r.y).to_equal(0.0)
```

</details>

#### dot product

#### computes dot product

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec2(1.0, 2.0)
val b = Vec2(3.0, 4.0)
expect(a.dot(b)).to_equal(11.0)
```

</details>

#### dot of perpendicular vectors is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec2(1.0, 0.0)
val b = Vec2(0.0, 1.0)
expect(a.dot(b)).to_equal(0.0)
```

</details>

#### magnitude

#### computes magnitude of (3, 4)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec2(3.0, 4.0)
expect(approx(v.magnitude(), 5.0)).to_equal(true)
```

</details>

#### magnitude of zero vector is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec2.zero()
expect(v.magnitude()).to_equal(0.0)
```

</details>

#### normalize

#### normalizes a non-zero vector to unit length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec2(3.0, 4.0)
val n = v.normalize()
expect(approx(n.magnitude(), 1.0)).to_equal(true)
```

</details>

#### normalize of zero vector returns zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec2.zero()
val n = v.normalize()
expect(n.x).to_equal(0.0)
expect(n.y).to_equal(0.0)
```

</details>

#### distance

#### computes distance between two points

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec2(0.0, 0.0)
val b = Vec2(3.0, 4.0)
expect(approx(a.distance(b), 5.0)).to_equal(true)
```

</details>

#### distance to self is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec2(1.0, 2.0)
expect(a.distance(a)).to_equal(0.0)
```

</details>

#### lerp

#### lerp at t=0 returns self

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec2(0.0, 0.0)
val b = Vec2(10.0, 10.0)
val r = a.lerp(b, 0.0)
expect(vec2_approx(r, a)).to_equal(true)
```

</details>

#### lerp at t=1 returns other

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec2(0.0, 0.0)
val b = Vec2(10.0, 10.0)
val r = a.lerp(b, 1.0)
expect(vec2_approx(r, b)).to_equal(true)
```

</details>

#### lerp at t=0.5 returns midpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec2(0.0, 0.0)
val b = Vec2(10.0, 20.0)
val r = a.lerp(b, 0.5)
expect(approx(r.x, 5.0)).to_equal(true)
expect(approx(r.y, 10.0)).to_equal(true)
```

</details>

#### predicates

#### is_zero returns true for zero vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Vec2.zero().is_zero()).to_equal(true)
```

</details>

#### is_zero returns false for non-zero vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Vec2(1.0, 0.0).is_zero()).to_equal(false)
```

</details>

#### is_near_zero returns true within epsilon

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec2(0.0001, 0.0001)
expect(v.is_near_zero(0.001)).to_equal(true)
```

</details>

#### is_near_zero returns false outside epsilon

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec2(1.0, 1.0)
expect(v.is_near_zero(0.001)).to_equal(false)
```

</details>

#### component_min and component_max

#### component_min picks smaller components

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec2(1.0, 5.0)
val b = Vec2(3.0, 2.0)
val r = a.component_min(b)
expect(r.x).to_equal(1.0)
expect(r.y).to_equal(2.0)
```

</details>

#### component_max picks larger components

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec2(1.0, 5.0)
val b = Vec2(3.0, 2.0)
val r = a.component_max(b)
expect(r.x).to_equal(3.0)
expect(r.y).to_equal(5.0)
```

</details>

### Vec3

#### constructors

#### zero returns (0, 0, 0)

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

#### one returns (1, 1, 1)

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

#### up is (0, 1, 0)

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

#### down is (0, -1, 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3.down()
expect(v.y).to_equal(-1.0)
```

</details>

#### left is (-1, 0, 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3.left()
expect(v.x).to_equal(-1.0)
```

</details>

#### right is (1, 0, 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3.right()
expect(v.x).to_equal(1.0)
```

</details>

#### forward is (0, 0, 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3.forward()
expect(v.z).to_equal(1.0)
```

</details>

#### back is (0, 0, -1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3.back()
expect(v.z).to_equal(-1.0)
```

</details>

#### arithmetic

#### adds two vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(1.0, 2.0, 3.0)
val b = Vec3(4.0, 5.0, 6.0)
val r = a.add(b)
expect(r.x).to_equal(5.0)
expect(r.y).to_equal(7.0)
expect(r.z).to_equal(9.0)
```

</details>

#### subtracts two vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(4.0, 5.0, 6.0)
val b = Vec3(1.0, 2.0, 3.0)
val r = a.sub(b)
expect(r.x).to_equal(3.0)
expect(r.y).to_equal(3.0)
expect(r.z).to_equal(3.0)
```

</details>

#### scales by scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3(1.0, 2.0, 3.0)
val r = v.scale(3.0)
expect(r.x).to_equal(3.0)
expect(r.y).to_equal(6.0)
expect(r.z).to_equal(9.0)
```

</details>

#### negates vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3(1.0, -2.0, 3.0)
val r = v.negate()
expect(r.x).to_equal(-1.0)
expect(r.y).to_equal(2.0)
expect(r.z).to_equal(-3.0)
```

</details>

#### dot product

#### computes dot product

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(1.0, 2.0, 3.0)
val b = Vec3(4.0, 5.0, 6.0)
expect(a.dot(b)).to_equal(32.0)
```

</details>

#### dot of perpendicular axis vectors is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Vec3.right().dot(Vec3.up())).to_equal(0.0)
```

</details>

#### cross product

#### right cross up = back (negative forward in some conventions)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Vec3.right().cross(Vec3.up())
expect(approx(r.x, 0.0)).to_equal(true)
expect(approx(r.y, 0.0)).to_equal(true)
expect(approx(r.z, -1.0)).to_equal(true)
```

</details>

#### cross product of parallel vectors is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(1.0, 0.0, 0.0)
val b = Vec3(2.0, 0.0, 0.0)
val r = a.cross(b)
expect(approx(r.magnitude(), 0.0)).to_equal(true)
```

</details>

#### magnitude

#### computes magnitude

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3(1.0, 2.0, 2.0)
expect(approx(v.magnitude(), 3.0)).to_equal(true)
```

</details>

#### unit vectors have magnitude 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(approx(Vec3.up().magnitude(), 1.0)).to_equal(true)
```

</details>

#### normalize

#### normalizes to unit length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3(3.0, 0.0, 4.0)
val n = v.normalize()
expect(approx(n.magnitude(), 1.0)).to_equal(true)
```

</details>

#### normalize zero vector returns zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3.zero()
val n = v.normalize()
expect(n.is_zero()).to_equal(true)
```

</details>

#### distance

#### computes distance

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(0.0, 0.0, 0.0)
val b = Vec3(1.0, 2.0, 2.0)
expect(approx(a.distance(b), 3.0)).to_equal(true)
```

</details>

#### lerp

#### lerp at t=0 returns self

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(1.0, 2.0, 3.0)
val b = Vec3(7.0, 8.0, 9.0)
val r = a.lerp(b, 0.0)
expect(vec3_approx(r, a)).to_equal(true)
```

</details>

#### lerp at t=1 returns other

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(1.0, 2.0, 3.0)
val b = Vec3(7.0, 8.0, 9.0)
val r = a.lerp(b, 1.0)
expect(vec3_approx(r, b)).to_equal(true)
```

</details>

#### lerp at t=0.5 returns midpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(0.0, 0.0, 0.0)
val b = Vec3(2.0, 4.0, 6.0)
val r = a.lerp(b, 0.5)
expect(approx(r.x, 1.0)).to_equal(true)
expect(approx(r.y, 2.0)).to_equal(true)
expect(approx(r.z, 3.0)).to_equal(true)
```

</details>

#### predicates

#### is_zero true for zero vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Vec3.zero().is_zero()).to_equal(true)
```

</details>

#### is_zero false for non-zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Vec3.up().is_zero()).to_equal(false)
```

</details>

#### is_near_zero within epsilon

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3(0.0001, 0.0001, 0.0001)
expect(v.is_near_zero(0.001)).to_equal(true)
```

</details>

#### is_near_zero outside epsilon

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Vec3.one().is_near_zero(0.001)).to_equal(false)
```

</details>

#### component_min and component_max

#### component_min

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(1.0, 5.0, 3.0)
val b = Vec3(4.0, 2.0, 6.0)
val r = a.component_min(b)
expect(r.x).to_equal(1.0)
expect(r.y).to_equal(2.0)
expect(r.z).to_equal(3.0)
```

</details>

#### component_max

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec3(1.0, 5.0, 3.0)
val b = Vec3(4.0, 2.0, 6.0)
val r = a.component_max(b)
expect(r.x).to_equal(4.0)
expect(r.y).to_equal(5.0)
expect(r.z).to_equal(6.0)
```

</details>

### Vec4

#### constructors

#### zero returns (0, 0, 0, 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec4.zero()
expect(v.x).to_equal(0.0)
expect(v.y).to_equal(0.0)
expect(v.z).to_equal(0.0)
expect(v.w).to_equal(0.0)
```

</details>

#### one returns (1, 1, 1, 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec4.one()
expect(v.x).to_equal(1.0)
expect(v.w).to_equal(1.0)
```

</details>

#### constructs with given values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec4(1.0, 2.0, 3.0, 4.0)
expect(v.x).to_equal(1.0)
expect(v.y).to_equal(2.0)
expect(v.z).to_equal(3.0)
expect(v.w).to_equal(4.0)
```

</details>

#### arithmetic

#### adds two vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec4(1.0, 2.0, 3.0, 4.0)
val b = Vec4(5.0, 6.0, 7.0, 8.0)
val r = a.add(b)
expect(r.x).to_equal(6.0)
expect(r.y).to_equal(8.0)
expect(r.z).to_equal(10.0)
expect(r.w).to_equal(12.0)
```

</details>

#### subtracts two vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec4(5.0, 6.0, 7.0, 8.0)
val b = Vec4(1.0, 2.0, 3.0, 4.0)
val r = a.sub(b)
expect(r.x).to_equal(4.0)
expect(r.w).to_equal(4.0)
```

</details>

#### scales by scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec4(1.0, 2.0, 3.0, 4.0)
val r = v.scale(2.0)
expect(r.x).to_equal(2.0)
expect(r.w).to_equal(8.0)
```

</details>

#### dot product

#### computes dot product

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec4(1.0, 2.0, 3.0, 4.0)
val b = Vec4(1.0, 1.0, 1.0, 1.0)
expect(a.dot(b)).to_equal(10.0)
```

</details>

#### magnitude

#### computes magnitude of (1, 0, 0, 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec4(1.0, 0.0, 0.0, 0.0)
expect(v.magnitude()).to_equal(1.0)
```

</details>

#### computes magnitude of (1, 1, 1, 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec4(1.0, 1.0, 1.0, 1.0)
expect(approx(v.magnitude(), 2.0)).to_equal(true)
```

</details>

#### normalize

#### normalizes to unit length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec4(2.0, 0.0, 0.0, 0.0)
val n = v.normalize()
expect(approx(n.magnitude(), 1.0)).to_equal(true)
```

</details>

#### normalize of zero returns zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec4.zero()
val n = v.normalize()
expect(n.is_zero()).to_equal(true)
```

</details>

#### lerp

#### lerp at t=0.5 returns midpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Vec4(0.0, 0.0, 0.0, 0.0)
val b = Vec4(2.0, 4.0, 6.0, 8.0)
val r = a.lerp(b, 0.5)
expect(approx(r.x, 1.0)).to_equal(true)
expect(approx(r.w, 4.0)).to_equal(true)
```

</details>

#### is_zero

#### is_zero true for zero vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Vec4.zero().is_zero()).to_equal(true)
```

</details>

#### is_zero false for non-zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Vec4.one().is_zero()).to_equal(false)
```

</details>

### Quat

#### identity

#### identity has w=1 and xyz=0

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

#### identity magnitude is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(approx(Quat.identity().magnitude(), 1.0)).to_equal(true)
```

</details>

#### from_axis_angle

#### from_axis_angle with zero angle gives identity-like quaternion

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = Quat.from_axis_angle(Vec3.up(), 0.0)
expect(approx(q.w, 1.0)).to_equal(true)
```

</details>

#### from_axis_angle produces unit quaternion

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = Quat.from_axis_angle(Vec3.up(), 1.0)
expect(approx(q.magnitude(), 1.0)).to_equal(true)
```

</details>

#### from_euler

#### zero euler angles gives near-identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = Quat.from_euler(0.0, 0.0, 0.0)
expect(approx(q.w, 1.0)).to_equal(true)
expect(approx(q.x, 0.0)).to_equal(true)
```

</details>

#### from_euler produces unit quaternion

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = Quat.from_euler(0.5, 0.3, 0.1)
expect(approx(q.magnitude(), 1.0)).to_equal(true)
```

</details>

#### magnitude and normalize

#### magnitude of identity is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(approx(Quat.identity().magnitude(), 1.0)).to_equal(true)
```

</details>

#### normalize of scaled quaternion returns unit

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = Quat(2.0, 0.0, 0.0, 0.0)
val n = q.normalize()
expect(approx(n.magnitude(), 1.0)).to_equal(true)
expect(approx(n.w, 1.0)).to_equal(true)
```

</details>

#### conjugate

#### conjugate negates xyz

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = Quat(0.5, 0.5, 0.5, 0.5)
val c = q.conjugate()
expect(c.w).to_equal(0.5)
expect(c.x).to_equal(-0.5)
expect(c.y).to_equal(-0.5)
expect(c.z).to_equal(-0.5)
```

</details>

#### inverse

#### identity inverse is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inv = Quat.identity().inverse()
expect(approx(inv.w, 1.0)).to_equal(true)
expect(approx(inv.x, 0.0)).to_equal(true)
```

</details>

#### q * q_inverse is near identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = Quat.from_axis_angle(Vec3.up(), 1.0)
val inv = q.inverse()
val product = q.mul(inv)
expect(approx(product.w, 1.0)).to_equal(true)
expect(approx(product.x, 0.0)).to_equal(true)
expect(approx(product.y, 0.0)).to_equal(true)
expect(approx(product.z, 0.0)).to_equal(true)
```

</details>

#### mul (composition)

#### identity * identity = identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = Quat.identity().mul(Quat.identity())
expect(quat_approx(q, Quat.identity())).to_equal(true)
```

</details>

#### identity * q = q

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = Quat.from_axis_angle(Vec3.up(), 1.0)
val r = Quat.identity().mul(q)
expect(quat_approx(r, q)).to_equal(true)
```

</details>

#### rotate_vector

#### identity rotation does not change vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Vec3(1.0, 2.0, 3.0)
val r = Quat.identity().rotate_vector(v)
expect(vec3_approx(r, v)).to_equal(true)
```

</details>

#### 180 degree rotation around Y flips X and Z

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = Quat.from_axis_angle(Vec3.up(), TAU * 0.5)
val v = Vec3(1.0, 0.0, 0.0)
val r = q.rotate_vector(v)
expect(approx(r.x, -1.0)).to_equal(true)
expect(approx(r.y, 0.0)).to_equal(true)
```

</details>

#### dot

#### dot of identity with itself is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = Quat.identity().dot(Quat.identity())
expect(approx(d, 1.0)).to_equal(true)
```

</details>

#### slerp

#### slerp at t=0 returns self

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Quat.identity()
val b = Quat.from_axis_angle(Vec3.up(), 1.0)
val r = a.slerp(b, 0.0)
expect(quat_approx(r, a)).to_equal(true)
```

</details>

#### slerp at t=1 returns other

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Quat.identity()
val b = Quat.from_axis_angle(Vec3.up(), 1.0)
val r = a.slerp(b, 1.0)
expect(quat_approx(r, b)).to_equal(true)
```

</details>

#### slerp result is unit quaternion

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Quat.from_axis_angle(Vec3.up(), 0.0)
val b = Quat.from_axis_angle(Vec3.up(), 1.0)
val r = a.slerp(b, 0.5)
expect(approx(r.magnitude(), 1.0)).to_equal(true)
```

</details>

#### to_mat4

<details>
<summary>Advanced: identity quaternion to_mat4 gives identity matrix</summary>

#### identity quaternion to_mat4 gives identity matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Quat.identity().to_mat4()
expect(approx(m.get(0, 0), 1.0)).to_equal(true)
expect(approx(m.get(1, 1), 1.0)).to_equal(true)
expect(approx(m.get(2, 2), 1.0)).to_equal(true)
expect(approx(m.get(3, 3), 1.0)).to_equal(true)
expect(approx(m.get(0, 1), 0.0)).to_equal(true)
expect(approx(m.get(0, 2), 0.0)).to_equal(true)
```

</details>


</details>

#### to_euler

#### identity quaternion has zero euler angles

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = Quat.identity().to_euler()
expect(approx(e.x, 0.0)).to_equal(true)
expect(approx(e.y, 0.0)).to_equal(true)
expect(approx(e.z, 0.0)).to_equal(true)
```

</details>

#### from_euler round-trips through to_euler

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = Quat.from_euler(0.3, 0.5, 0.1)
val e = q.to_euler()
val q2 = Quat.from_euler(e.x, e.y, e.z)
expect(quat_approx(q, q2)).to_equal(true)
```

</details>

### Mat4

#### identity

#### diagonal is 1, off-diagonal is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mat4.identity()
expect(m.get(0, 0)).to_equal(1.0)
expect(m.get(1, 1)).to_equal(1.0)
expect(m.get(2, 2)).to_equal(1.0)
expect(m.get(3, 3)).to_equal(1.0)
expect(m.get(0, 1)).to_equal(0.0)
expect(m.get(1, 0)).to_equal(0.0)
```

</details>

#### translation

<details>
<summary>Advanced: translation matrix contains translation in column 3</summary>

#### translation matrix contains translation in column 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mat4.translation(2.0, 3.0, 4.0)
expect(approx(m.get(0, 3), 2.0)).to_equal(true)
expect(approx(m.get(1, 3), 3.0)).to_equal(true)
expect(approx(m.get(2, 3), 4.0)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: translation matrix transforms a point</summary>

#### translation matrix transforms a point

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mat4.translation(1.0, 2.0, 3.0)
val p = Vec3(0.0, 0.0, 0.0)
val r = m.transform_point(p)
expect(approx(r.x, 1.0)).to_equal(true)
expect(approx(r.y, 2.0)).to_equal(true)
expect(approx(r.z, 3.0)).to_equal(true)
```

</details>


</details>

#### rotation_x

#### rotation_x by zero is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mat4.rotation_x(0.0)
expect(approx(m.get(0, 0), 1.0)).to_equal(true)
expect(approx(m.get(1, 1), 1.0)).to_equal(true)
```

</details>

#### rotation_x by 90 degrees rotates up to forward

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val angle = PI * 0.5
val m = Mat4.rotation_x(angle)
val up = Vec3(0.0, 1.0, 0.0)
val r = m.transform_vec3(up)
expect(approx(r.x, 0.0)).to_equal(true)
expect(approx(r.y, 0.0)).to_equal(true)
expect(approx(r.z, 1.0)).to_equal(true)
```

</details>

#### rotation_y

#### rotation_y by 90 degrees rotates forward to right

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val angle = PI * 0.5
val m = Mat4.rotation_y(angle)
val fwd = Vec3(0.0, 0.0, 1.0)
val r = m.transform_vec3(fwd)
expect(approx(r.x, 1.0)).to_equal(true)
expect(approx(r.y, 0.0)).to_equal(true)
expect(approx(r.z, 0.0)).to_equal(true)
```

</details>

#### rotation_z

#### rotation_z by zero is identity-like

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mat4.rotation_z(0.0)
expect(approx(m.get(0, 0), 1.0)).to_equal(true)
```

</details>

#### rotation_z by 90 degrees rotates right to up

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val angle = PI * 0.5
val m = Mat4.rotation_z(angle)
val right = Vec3(1.0, 0.0, 0.0)
val r = m.transform_vec3(right)
expect(approx(r.x, 0.0)).to_equal(true)
expect(approx(r.y, 1.0)).to_equal(true)
expect(approx(r.z, 0.0)).to_equal(true)
```

</details>

#### scaling

<details>
<summary>Advanced: scaling matrix scales a vector</summary>

#### scaling matrix scales a vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mat4.scaling(2.0, 3.0, 4.0)
val v = Vec3(1.0, 1.0, 1.0)
val r = m.transform_vec3(v)
expect(approx(r.x, 2.0)).to_equal(true)
expect(approx(r.y, 3.0)).to_equal(true)
expect(approx(r.z, 4.0)).to_equal(true)
```

</details>


</details>

#### uniform scaling by 1 gives same vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mat4.scaling(1.0, 1.0, 1.0)
val v = Vec3(5.0, 6.0, 7.0)
val r = m.transform_vec3(v)
expect(vec3_approx(r, v)).to_equal(true)
```

</details>

#### perspective

<details>
<summary>Advanced: perspective matrix is non-trivial</summary>

#### perspective matrix is non-trivial

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mat4.perspective(PI * 0.5, 1.0, 0.1, 100.0)
expect(m.get(0, 0)).to_be_greater_than(0.0)
```

</details>


</details>

#### ortho

<details>
<summary>Advanced: ortho matrix is non-trivial</summary>

#### ortho matrix is non-trivial

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mat4.ortho(-1.0, 1.0, -1.0, 1.0, 0.1, 100.0)
expect(m.get(0, 0)).to_be_greater_than(0.0)
```

</details>


</details>

#### look_at

<details>
<summary>Advanced: look_at from origin to forward creates valid matrix</summary>

#### look_at from origin to forward creates valid matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eye = Vec3(0.0, 0.0, 0.0)
val center = Vec3(0.0, 0.0, -1.0)
val up = Vec3(0.0, 1.0, 0.0)
val m = Mat4.look_at(eye, center, up)
expect(approx(m.get(3, 3), 1.0)).to_equal(true)
```

</details>


</details>

#### get

<details>
<summary>Advanced: get reads identity matrix correctly</summary>

#### get reads identity matrix correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mat4.identity()
expect(m.get(0, 0)).to_equal(1.0)
expect(m.get(1, 1)).to_equal(1.0)
expect(m.get(0, 1)).to_equal(0.0)
```

</details>


</details>

#### mul

#### identity * identity = identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mat4.identity().mul(Mat4.identity())
expect(approx(m.get(0, 0), 1.0)).to_equal(true)
expect(approx(m.get(1, 1), 1.0)).to_equal(true)
expect(approx(m.get(0, 1), 0.0)).to_equal(true)
```

</details>

#### identity * m = m

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mat4.translation(1.0, 2.0, 3.0)
val r = Mat4.identity().mul(m)
expect(approx(r.get(0, 3), 1.0)).to_equal(true)
expect(approx(r.get(1, 3), 2.0)).to_equal(true)
expect(approx(r.get(2, 3), 3.0)).to_equal(true)
```

</details>

#### transpose

#### transpose of identity is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mat4.identity().transpose()
expect(approx(m.get(0, 0), 1.0)).to_equal(true)
expect(approx(m.get(0, 1), 0.0)).to_equal(true)
```

</details>

#### transpose swaps row and column

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mat4.translation(1.0, 2.0, 3.0)
val t = m.transpose()
expect(approx(t.get(3, 0), 1.0)).to_equal(true)
expect(approx(t.get(3, 1), 2.0)).to_equal(true)
expect(approx(t.get(3, 2), 3.0)).to_equal(true)
```

</details>

#### transform_point

#### identity transform_point leaves point unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mat4.identity()
val p = Vec3(1.0, 2.0, 3.0)
val r = m.transform_point(p)
expect(vec3_approx(r, p)).to_equal(true)
```

</details>

#### translation transform_point shifts the point

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mat4.translation(5.0, 0.0, 0.0)
val p = Vec3(1.0, 0.0, 0.0)
val r = m.transform_point(p)
expect(approx(r.x, 6.0)).to_equal(true)
```

</details>

#### transform_vec3

#### identity transform_vec3 leaves vector unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mat4.identity()
val v = Vec3(1.0, 2.0, 3.0)
val r = m.transform_vec3(v)
expect(vec3_approx(r, v)).to_equal(true)
```

</details>

#### translation does not affect direction vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Mat4.translation(10.0, 10.0, 10.0)
val v = Vec3(1.0, 0.0, 0.0)
val r = m.transform_vec3(v)
expect(vec3_approx(r, v)).to_equal(true)
```

</details>

### Transform

#### identity

#### identity has zero position

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform.identity()
expect(t.position.is_zero()).to_equal(true)
```

</details>

#### identity has unit scale

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform.identity()
expect(vec3_approx(t.scale_, Vec3.one())).to_equal(true)
```

</details>

#### identity rotation is identity quat

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform.identity()
expect(quat_approx(t.rotation, Quat.identity())).to_equal(true)
```

</details>

#### to_mat4

<details>
<summary>Advanced: identity transform to_mat4 gives identity matrix</summary>

#### identity transform to_mat4 gives identity matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Transform.identity().to_mat4()
expect(approx(m.get(0, 0), 1.0)).to_equal(true)
expect(approx(m.get(1, 1), 1.0)).to_equal(true)
expect(approx(m.get(2, 2), 1.0)).to_equal(true)
expect(approx(m.get(3, 3), 1.0)).to_equal(true)
```

</details>


</details>

#### directional helpers

#### identity forward is (0, 0, 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform.identity()
val f = t.forward()
expect(vec3_approx(f, Vec3.forward())).to_equal(true)
```

</details>

#### identity right_dir is (1, 0, 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform.identity()
val r = t.right_dir()
expect(vec3_approx(r, Vec3.right())).to_equal(true)
```

</details>

#### identity up_dir is (0, 1, 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform.identity()
val u = t.up_dir()
expect(vec3_approx(u, Vec3.up())).to_equal(true)
```

</details>

#### inverse

#### identity inverse is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inv = Transform.identity().inverse()
expect(vec3_approx(inv.position, Vec3.zero())).to_equal(true)
expect(vec3_approx(inv.scale_, Vec3.one())).to_equal(true)
```

</details>

#### transform combined with inverse produces near-identity position

1. position: Vec3
2. rotation: Quat identity
3. scale : Vec3 one
   - Expected: vec3_approx(combined.position, Vec3.zero()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform(
    position: Vec3(1.0, 2.0, 3.0),
    rotation: Quat.identity(),
    scale_: Vec3.one()
)
val inv = t.inverse()
val combined = t.combine(inv)
expect(vec3_approx(combined.position, Vec3.zero())).to_equal(true)
```

</details>

#### lerp

#### lerp at t=0 returns self position

1. position: Vec3
2. rotation: Quat identity
3. scale : Vec3 one
   - Expected: vec3_approx(r.position, Vec3.zero()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Transform.identity()
val b = Transform(
    position: Vec3(10.0, 0.0, 0.0),
    rotation: Quat.identity(),
    scale_: Vec3.one()
)
val r = a.lerp(b, 0.0)
expect(vec3_approx(r.position, Vec3.zero())).to_equal(true)
```

</details>

#### lerp at t=1 returns other position

1. position: Vec3
2. rotation: Quat identity
3. scale : Vec3 one
   - Expected: approx(r.position.x, 10.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Transform.identity()
val b = Transform(
    position: Vec3(10.0, 0.0, 0.0),
    rotation: Quat.identity(),
    scale_: Vec3.one()
)
val r = a.lerp(b, 1.0)
expect(approx(r.position.x, 10.0)).to_equal(true)
```

</details>

#### combine

#### identity combine identity is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Transform.identity().combine(Transform.identity())
expect(vec3_approx(r.position, Vec3.zero())).to_equal(true)
expect(vec3_approx(r.scale_, Vec3.one())).to_equal(true)
```

</details>

#### transform_point

#### identity transform_point is unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform.identity()
val p = Vec3(1.0, 2.0, 3.0)
val r = t.transform_point(p)
expect(vec3_approx(r, p)).to_equal(true)
```

</details>

#### translate then transform_point offsets point

1. position: Vec3
2. rotation: Quat identity
3. scale : Vec3 one
   - Expected: approx(r.x, 1.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform(
    position: Vec3(1.0, 0.0, 0.0),
    rotation: Quat.identity(),
    scale_: Vec3.one()
)
val p = Vec3(0.0, 0.0, 0.0)
val r = t.transform_point(p)
expect(approx(r.x, 1.0)).to_equal(true)
```

</details>

#### transform_vector

#### identity transform_vector is unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform.identity()
val v = Vec3(1.0, 0.0, 0.0)
val r = t.transform_vector(v)
expect(vec3_approx(r, v)).to_equal(true)
```

</details>

#### scale transform_vector scales the vector

1. position: Vec3 zero
2. rotation: Quat identity
3. scale : Vec3
   - Expected: approx(r.x, 2.0) is true
   - Expected: approx(r.y, 2.0) is true
   - Expected: approx(r.z, 2.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transform(
    position: Vec3.zero(),
    rotation: Quat.identity(),
    scale_: Vec3(2.0, 2.0, 2.0)
)
val v = Vec3(1.0, 1.0, 1.0)
val r = t.transform_vector(v)
expect(approx(r.x, 2.0)).to_equal(true)
expect(approx(r.y, 2.0)).to_equal(true)
expect(approx(r.z, 2.0)).to_equal(true)
```

</details>

### AABB

#### constructor

#### stores min and max

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box = AABB(min: Vec3(-1.0, -1.0, -1.0), max: Vec3(1.0, 1.0, 1.0))
expect(vec3_approx(box.min, Vec3(-1.0, -1.0, -1.0))).to_equal(true)
expect(vec3_approx(box.max, Vec3(1.0, 1.0, 1.0))).to_equal(true)
```

</details>

#### from_center_extents

#### creates box from center and half-extents

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box = AABB.from_center_extents(Vec3.zero(), Vec3.one())
expect(vec3_approx(box.min, Vec3(-1.0, -1.0, -1.0))).to_equal(true)
expect(vec3_approx(box.max, Vec3(1.0, 1.0, 1.0))).to_equal(true)
```

</details>

#### center

#### center of unit box at origin is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box = AABB(min: Vec3(-1.0, -1.0, -1.0), max: Vec3(1.0, 1.0, 1.0))
val c = box.center()
expect(vec3_approx(c, Vec3.zero())).to_equal(true)
```

</details>

#### center of offset box is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box = AABB(min: Vec3(0.0, 0.0, 0.0), max: Vec3(2.0, 4.0, 6.0))
val c = box.center()
expect(approx(c.x, 1.0)).to_equal(true)
expect(approx(c.y, 2.0)).to_equal(true)
expect(approx(c.z, 3.0)).to_equal(true)
```

</details>

#### extents

#### extents of unit box is (1, 1, 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box = AABB(min: Vec3(-1.0, -1.0, -1.0), max: Vec3(1.0, 1.0, 1.0))
val e = box.extents()
expect(vec3_approx(e, Vec3.one())).to_equal(true)
```

</details>

#### size

#### size of 2x2x2 box is (2, 2, 2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box = AABB(min: Vec3(-1.0, -1.0, -1.0), max: Vec3(1.0, 1.0, 1.0))
val s = box.size()
expect(vec3_approx(s, Vec3(2.0, 2.0, 2.0))).to_equal(true)
```

</details>

#### contains_point

#### contains center point

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box = AABB(min: Vec3(-1.0, -1.0, -1.0), max: Vec3(1.0, 1.0, 1.0))
expect(box.contains_point(Vec3.zero())).to_equal(true)
```

</details>

#### contains corner point

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box = AABB(min: Vec3(-1.0, -1.0, -1.0), max: Vec3(1.0, 1.0, 1.0))
expect(box.contains_point(Vec3(1.0, 1.0, 1.0))).to_equal(true)
```

</details>

#### does not contain outside point

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box = AABB(min: Vec3(-1.0, -1.0, -1.0), max: Vec3(1.0, 1.0, 1.0))
expect(box.contains_point(Vec3(2.0, 0.0, 0.0))).to_equal(false)
```

</details>

#### intersects

#### overlapping boxes intersect

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = AABB(min: Vec3(-1.0, -1.0, -1.0), max: Vec3(1.0, 1.0, 1.0))
val b = AABB(min: Vec3(0.0, 0.0, 0.0), max: Vec3(2.0, 2.0, 2.0))
expect(a.intersects(b)).to_equal(true)
```

</details>

#### non-overlapping boxes do not intersect

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = AABB(min: Vec3(-1.0, -1.0, -1.0), max: Vec3(0.0, 0.0, 0.0))
val b = AABB(min: Vec3(1.0, 1.0, 1.0), max: Vec3(2.0, 2.0, 2.0))
expect(a.intersects(b)).to_equal(false)
```

</details>

#### touching boxes intersect

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = AABB(min: Vec3(-1.0, -1.0, -1.0), max: Vec3(1.0, 1.0, 1.0))
val b = AABB(min: Vec3(1.0, -1.0, -1.0), max: Vec3(2.0, 1.0, 1.0))
expect(a.intersects(b)).to_equal(true)
```

</details>

#### expand

#### expands to union of two boxes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = AABB(min: Vec3(-1.0, -1.0, -1.0), max: Vec3(0.0, 0.0, 0.0))
val b = AABB(min: Vec3(0.0, 0.0, 0.0), max: Vec3(1.0, 1.0, 1.0))
val r = a.expand(b)
expect(vec3_approx(r.min, Vec3(-1.0, -1.0, -1.0))).to_equal(true)
expect(vec3_approx(r.max, Vec3(1.0, 1.0, 1.0))).to_equal(true)
```

</details>

### Ray

#### constructor

#### auto-normalizes direction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ray.create(origin: Vec3.zero(), direction: Vec3(0.0, 0.0, 5.0))
expect(approx(r.direction.magnitude(), 1.0)).to_equal(true)
```

</details>

#### stores origin

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ray.create(origin: Vec3(1.0, 2.0, 3.0), direction: Vec3(0.0, 0.0, 1.0))
expect(vec3_approx(r.origin, Vec3(1.0, 2.0, 3.0))).to_equal(true)
```

</details>

#### normalized direction is unit length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ray.create(origin: Vec3.zero(), direction: Vec3(3.0, 4.0, 0.0))
expect(approx(r.direction.magnitude(), 1.0)).to_equal(true)
```

</details>

#### point_at

#### point_at t=0 returns origin

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ray.create(origin: Vec3(1.0, 2.0, 3.0), direction: Vec3(0.0, 0.0, 1.0))
val p = r.point_at(0.0)
expect(vec3_approx(p, r.origin)).to_equal(true)
```

</details>

#### point_at t=1 returns origin + direction

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ray.create(origin: Vec3.zero(), direction: Vec3(0.0, 0.0, 1.0))
val p = r.point_at(1.0)
expect(approx(p.z, 1.0)).to_equal(true)
```

</details>

#### point_at t=5 returns 5 units along direction

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ray.create(origin: Vec3.zero(), direction: Vec3(1.0, 0.0, 0.0))
val p = r.point_at(5.0)
expect(approx(p.x, 5.0)).to_equal(true)
```

</details>

### Constants

#### PI is approximately 3.14159

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(approx(PI, 3.14159)).to_equal(true)
```

</details>

#### TAU is approximately 6.28318

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(approx(TAU, 6.28318)).to_equal(true)
```

</details>

#### TAU is 2 * PI

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(approx(TAU, PI * 2.0)).to_equal(true)
```

</details>

#### DEG_TO_RAD * RAD_TO_DEG is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(approx(DEG_TO_RAD * RAD_TO_DEG, 1.0)).to_equal(true)
```

</details>

#### DEG_TO_RAD converts 180 to PI

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(approx(180.0 * DEG_TO_RAD, PI)).to_equal(true)
```

</details>

#### RAD_TO_DEG converts PI to 180

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(approx(PI * RAD_TO_DEG, 180.0)).to_equal(true)
```

</details>

### Helper functions

#### to_radians

#### converts 0 degrees to 0 radians

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_radians(0.0)).to_equal(0.0)
```

</details>

#### converts 180 degrees to PI

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(approx(to_radians(180.0), PI)).to_equal(true)
```

</details>

#### converts 360 degrees to TAU

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(approx(to_radians(360.0), TAU)).to_equal(true)
```

</details>

#### to_degrees

#### converts 0 radians to 0 degrees

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_degrees(0.0)).to_equal(0.0)
```

</details>

#### converts PI to 180 degrees

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(approx(to_degrees(PI), 180.0)).to_equal(true)
```

</details>

#### round-trips with to_radians

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(approx(to_degrees(to_radians(90.0)), 90.0)).to_equal(true)
```

</details>

#### clamp

#### clamps value below min

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp(-5.0, 0.0, 1.0)).to_equal(0.0)
```

</details>

#### clamps value above max

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp(10.0, 0.0, 1.0)).to_equal(1.0)
```

</details>

#### returns value within range unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp(0.5, 0.0, 1.0)).to_equal(0.5)
```

</details>

#### clamps to min when equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp(0.0, 0.0, 1.0)).to_equal(0.0)
```

</details>

#### clamps to max when equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clamp(1.0, 0.0, 1.0)).to_equal(1.0)
```

</details>

#### lerp_f32

#### lerp at t=0 returns a

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lerp_f32(0.0, 10.0, 0.0)).to_equal(0.0)
```

</details>

#### lerp at t=1 returns b

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lerp_f32(0.0, 10.0, 1.0)).to_equal(10.0)
```

</details>

#### lerp at t=0.5 returns midpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(approx(lerp_f32(0.0, 10.0, 0.5), 5.0)).to_equal(true)
```

</details>

#### lerp with negative values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(approx(lerp_f32(-10.0, 10.0, 0.5), 0.0)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/game3d/math_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Vec2
- Vec3
- Vec4
- Quat
- Mat4
- Transform
- AABB
- Ray
- Constants
- Helper functions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 168 |
| Active scenarios | 168 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
