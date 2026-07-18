# Physics 3d Collision Specification

> <details>

<!-- sdn-diagram:id=physics_3d_collision_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=physics_3d_collision_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

physics_3d_collision_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=physics_3d_collision_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics 3d Collision Specification

## Scenarios

### Physics2 3D Collision

#### sphere-sphere overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = collide_sphere_sphere(0.0, 0.0, 0.0, 1.0, 1.5, 0.0, 0.0, 1.0)
expect(c.has_contact).to_equal(true)
expect(c.penetration).to_equal(0.5)
```

</details>

#### sphere-sphere miss

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = collide_sphere_sphere(0.0, 0.0, 0.0, 1.0, 5.0, 0.0, 0.0, 1.0)
expect(c.has_contact).to_equal(false)
```

</details>

#### sphere-box overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = collide_sphere_aabb_3d(1.4, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0, 1.0, 1.0)
expect(c.has_contact).to_equal(true)
```

</details>

#### sphere-box miss

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = collide_sphere_aabb_3d(5.0, 0.0, 0.0, 0.5, 0.0, 0.0, 0.0, 1.0, 1.0, 1.0)
expect(c.has_contact).to_equal(false)
```

</details>

#### box-box overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = collide_aabb_aabb_3d(0.0, 0.0, 0.0, 1.0, 1.0, 1.0, 1.5, 0.0, 0.0, 1.0, 1.0, 1.0)
expect(c.has_contact).to_equal(true)
```

</details>

#### box-box separated

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = collide_aabb_aabb_3d(0.0, 0.0, 0.0, 1.0, 1.0, 1.0, 5.0, 0.0, 0.0, 1.0, 1.0, 1.0)
expect(c.has_contact).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_3d_collision_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Physics2 3D Collision

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
