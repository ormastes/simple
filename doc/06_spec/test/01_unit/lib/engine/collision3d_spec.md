# collision3d_spec

> Engine Collision 3D — Narrow-phase 3D collision detection tests

<!-- sdn-diagram:id=collision3d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=collision3d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

collision3d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=collision3d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# collision3d_spec

Engine Collision 3D — Narrow-phase 3D collision detection tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/collision3d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Collision 3D — Narrow-phase 3D collision detection tests

Tests sphere-sphere, AABB-AABB, sphere-AABB, and OBB-OBB collision
detection functions. Uses the pure Simple 3D collision module.

## Scenarios

### Collision3D sphere-sphere

#### overlapping returns contact

1. Vec3
2. Vec3
   - Expected: is_contact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contact = collide_sphere_sphere(
    Vec3(x: 0.0, y: 0.0, z: 0.0), 1.0,
    Vec3(x: 1.5, y: 0.0, z: 0.0), 1.0
)
# In interpreter Option::Some(x) unwraps to x directly
val is_contact = contact != nil
expect(is_contact).to_equal(true)
if is_contact:
    val pen = contact.penetration * 100.0
    expect(pen).to_be_greater_than(49.0)
    expect(pen).to_be_less_than(51.0)
```

</details>

#### non-overlapping returns nil

1. Vec3
2. Vec3


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contact = collide_sphere_sphere(
    Vec3(x: 0.0, y: 0.0, z: 0.0), 1.0,
    Vec3(x: 5.0, y: 0.0, z: 0.0), 1.0
)
expect(contact).to_be_nil()
```

</details>

### Collision3D AABB-AABB

#### overlapping returns contact

1. Vec3
2. Vec3
   - Expected: is_contact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contact = collide_aabb_aabb(
    Vec3(x: 0.0, y: 0.0, z: 0.0), Vec3(x: 1.0, y: 1.0, z: 1.0),
    Vec3(x: 1.5, y: 0.0, z: 0.0), Vec3(x: 1.0, y: 1.0, z: 1.0)
)
val is_contact = contact != nil
expect(is_contact).to_equal(true)
if is_contact:
    expect(contact.penetration).to_be_greater_than(0.0)
```

</details>

#### separated returns nil

1. Vec3
2. Vec3


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contact = collide_aabb_aabb(
    Vec3(x: 0.0, y: 0.0, z: 0.0), Vec3(x: 1.0, y: 1.0, z: 1.0),
    Vec3(x: 5.0, y: 0.0, z: 0.0), Vec3(x: 1.0, y: 1.0, z: 1.0)
)
expect(contact).to_be_nil()
```

</details>

### Collision3D sphere-AABB

#### sphere inside box

1. Vec3
2. Vec3
   - Expected: is_contact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contact = collide_sphere_aabb(
    Vec3(x: 0.0, y: 0.0, z: 0.0), 0.5,
    Vec3(x: 0.0, y: 0.0, z: 0.0), Vec3(x: 2.0, y: 2.0, z: 2.0)
)
val is_contact = contact != nil
expect(is_contact).to_equal(true)
if is_contact:
    expect(contact.penetration).to_be_greater_than(0.0)
```

</details>

#### sphere outside box

1. Vec3
2. Vec3


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contact = collide_sphere_aabb(
    Vec3(x: 10.0, y: 0.0, z: 0.0), 0.5,
    Vec3(x: 0.0, y: 0.0, z: 0.0), Vec3(x: 1.0, y: 1.0, z: 1.0)
)
expect(contact).to_be_nil()
```

</details>

### Collision3D OBB-OBB

#### aligned boxes overlap

1. Vec3
2. Vec3
   - Expected: is_contact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# OBB with identity rotation = AABB
val identity = Quaternion.identity()
val contact = collide_obb_obb(
    Vec3(x: 0.0, y: 0.0, z: 0.0), Vec3(x: 1.0, y: 1.0, z: 1.0), identity,
    Vec3(x: 1.5, y: 0.0, z: 0.0), Vec3(x: 1.0, y: 1.0, z: 1.0), identity
)
val is_contact = contact != nil
expect(is_contact).to_equal(true)
if is_contact:
    expect(contact.penetration).to_be_greater_than(0.0)
```

</details>

#### separated boxes

1. Vec3
2. Vec3


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val identity = Quaternion.identity()
val contact = collide_obb_obb(
    Vec3(x: 0.0, y: 0.0, z: 0.0), Vec3(x: 1.0, y: 1.0, z: 1.0), identity,
    Vec3(x: 10.0, y: 0.0, z: 0.0), Vec3(x: 1.0, y: 1.0, z: 1.0), identity
)
expect(contact).to_be_nil()
```

</details>

### Collision3D contact normal

#### contact normal points from A to B

1. Vec3
2. Vec3
   - Expected: is_contact is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contact = collide_sphere_sphere(
    Vec3(x: 0.0, y: 0.0, z: 0.0), 1.0,
    Vec3(x: 1.0, y: 0.0, z: 0.0), 1.0
)
val is_contact = contact != nil
expect(is_contact).to_equal(true)
if is_contact:
    # Normal should point from A to B, so x > 0
    expect(contact.normal.x).to_be_greater_than(0.0)
    # Y and Z should be approximately zero
    val ny_i = contact.normal.y * 1000.0
    val nz_i = contact.normal.z * 1000.0
    expect(ny_i).to_be_greater_than(-1.0)
    expect(ny_i).to_be_less_than(1.0)
    expect(nz_i).to_be_greater_than(-1.0)
    expect(nz_i).to_be_less_than(1.0)
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
