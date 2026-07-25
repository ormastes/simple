# Physics Joints Specification

> <details>

<!-- sdn-diagram:id=physics_joints_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=physics_joints_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

physics_joints_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=physics_joints_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics Joints Specification

## Scenarios

### Physics2 Joints

#### distance joint force at stretch

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ba = make_body(0)
val bb = make_body(1)
val dj = DistanceJoint.new(ba, bb, 2.0)
val force = dj.compute_force(0.0, 0.0, 3.0, 0.0)
# bodies at (0,0) and (3,0), rest=2.0 => stretch=1.0, stiffness=1.0 => fx=1.0
expect(math_abs(force.fx)).to_be_greater_than(0.0)
```

</details>

#### distance joint zero force at rest

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ba = make_body(0)
val bb = make_body(1)
val dj = DistanceJoint.new(ba, bb, 2.0)
val force = dj.compute_force(0.0, 0.0, 2.0, 0.0)
# dist == rest_length => stretch == 0 => force == 0
expect(math_abs(force.fx)).to_be_less_than(0.0001)
```

</details>

#### spring joint Hooke law

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mag = check_spring_force_magnitude()
expect(mag).to_be_greater_than(0.0)
```

</details>

#### revolute joint with limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ba = make_body(0)
val bb = make_body(1)
val rj = RevoluteJoint.with_limits(ba, bb, 0.0, 0.0, -1.0, 1.0)
expect(rj.enable_limit).to_equal(true)
```

</details>

#### prismatic joint normalizes axis

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ba = make_body(0)
val bb = make_body(1)
val pj = PrismaticJoint.new(ba, bb, 0.0, 0.0, 3.0, 4.0)
# norm = 3/5 = 0.6
expect(pj.axis_x).to_be_greater_than(0.599)
expect(pj.axis_x).to_be_less_than(0.601)
```

</details>

#### weld joint stores anchor

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ba = make_body(0)
val bb = make_body(1)
val wj = WeldJoint.new(ba, bb, 1.5, 2.5)
expect(wj.anchor_x).to_equal(1.5)
```

</details>

#### registry add and count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = build_registry_three()
expect(reg.joint_count()).to_equal(3)
```

</details>

#### registry remove

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = build_registry_remove()
expect(reg.joint_count()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_joints_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Physics2 Joints

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
