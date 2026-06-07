# Joints Specification

> 1. check

<!-- sdn-diagram:id=joints_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=joints_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

joints_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=joints_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Joints Specification

## Scenarios

### Physics Constraints

#### Distance Joint

#### constrains distance between bodies

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b1 = JointBody.new(0.0, 0.0, 5.0)
val b2 = JointBody.new(10.0, 0.0, 5.0)
val joint = DistanceJoint.new(b1, b2, 10.0)
check(joint.distance == 10.0)
```

</details>

#### applies correction force

1. joint apply correction
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b1 = JointBody.new(0.0, 0.0, 5.0)
val b2 = JointBody.new(10.0, 0.0, 5.0)
val joint = DistanceJoint.new(b1, b2, 10.0)
joint.apply_correction()
check(joint.get_correction_force() == 1.0)
```

</details>

#### Hinge Joint

#### allows rotation around axis

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b1 = JointBody.new(0.0, 0.0, 5.0)
val b2 = JointBody.new(0.0, 1.0, 5.0)
val joint = HingeJoint.new(b1, b2)
check(joint.is_enabled() == true)
```

</details>

#### applies angular limits

1. joint set angular limit
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b1 = JointBody.new(0.0, 0.0, 5.0)
val b2 = JointBody.new(0.0, 1.0, 5.0)
val joint = HingeJoint.new(b1, b2)
joint.set_angular_limit(45.0)
check(joint.get_angular_limit() == 45.0)
```

</details>

#### Slider Joint

#### allows linear movement

1. joint set position
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b1 = JointBody.new(0.0, 0.0, 5.0)
val b2 = JointBody.new(1.0, 0.0, 5.0)
val joint = SliderJoint.new(b1, b2)
joint.set_position(5.0)
check(joint.get_position() == 5.0)
```

</details>

#### applies linear limits

1. joint set linear limit
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b1 = JointBody.new(0.0, 0.0, 5.0)
val b2 = JointBody.new(1.0, 0.0, 5.0)
val joint = SliderJoint.new(b1, b2)
joint.set_linear_limit(20.0)
check(joint.linear_limit == 20.0)
```

</details>

#### Fixed Joint

#### locks bodies together

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b1 = JointBody.new(0.0, 0.0, 5.0)
val b2 = JointBody.new(1.0, 0.0, 5.0)
val joint = FixedJoint.new(b1, b2)
check(joint.is_locked() == true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/physics/joints_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Physics Constraints

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
