# Joints Specification

> Tests covering Physics Constraints.

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

- constrains distance between bodies


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constrains distance between bodies")
val b1 = JointBody.new(0.0, 0.0, 5.0)
val b2 = JointBody.new(10.0, 0.0, 5.0)
val joint = DistanceJoint.new(b1, b2, 10.0)
check(joint.distance == 10.0)
```

</details>

#### applies correction force

- applies correction force


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies correction force")
val b1 = JointBody.new(0.0, 0.0, 5.0)
val b2 = JointBody.new(10.0, 0.0, 5.0)
val joint = DistanceJoint.new(b1, b2, 10.0)
joint.apply_correction()
check(joint.get_correction_force() == 1.0)
```

</details>

#### Hinge Joint

#### allows rotation around axis

- allows rotation around axis


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows rotation around axis")
val b1 = JointBody.new(0.0, 0.0, 5.0)
val b2 = JointBody.new(0.0, 1.0, 5.0)
val joint = HingeJoint.new(b1, b2)
check(joint.is_enabled() == true)
```

</details>

#### applies angular limits

- applies angular limits


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies angular limits")
val b1 = JointBody.new(0.0, 0.0, 5.0)
val b2 = JointBody.new(0.0, 1.0, 5.0)
val joint = HingeJoint.new(b1, b2)
joint.set_angular_limit(45.0)
check(joint.get_angular_limit() == 45.0)
```

</details>

#### Slider Joint

#### allows linear movement

- allows linear movement


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows linear movement")
val b1 = JointBody.new(0.0, 0.0, 5.0)
val b2 = JointBody.new(1.0, 0.0, 5.0)
val joint = SliderJoint.new(b1, b2)
joint.set_position(5.0)
check(joint.get_position() == 5.0)
```

</details>

#### applies linear limits

- applies linear limits


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies linear limits")
val b1 = JointBody.new(0.0, 0.0, 5.0)
val b2 = JointBody.new(1.0, 0.0, 5.0)
val joint = SliderJoint.new(b1, b2)
joint.set_linear_limit(20.0)
check(joint.linear_limit == 20.0)
```

</details>

#### Fixed Joint

#### locks bodies together

- locks bodies together


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("locks bodies together")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Physics Constraints.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8b3033306721eed8389d48f8f82efa096197572dee9f3fbb23700c8b55cd276e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b3033306721eed8389d48f8f82efa096197572dee9f3fbb23700c8b55cd276e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b3033306721eed8389d48f8f82efa096197572dee9f3fbb23700c8b55cd276e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/physics/joints_spec.spl
mirror: doc/06_spec/01_unit/lib/physics/joints_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/physics/joints_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/physics/joints_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/physics/joints_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constrains distance between bodies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/physics/joints_spec.spl:120:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies correction force' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/physics/joints_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows rotation around axis' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
