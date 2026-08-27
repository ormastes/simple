# Physics 3d Smoke Specification

> Tests covering Physics2 3D Smoke Test.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics 3d Smoke Specification

## Scenarios

### Physics2 3D Smoke Test

#### sphere falls under gravity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sphere falls under gravity
   - Expected: pos.y < 10.0 is true
   - Expected: pos.y > -50.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sphere falls under gravity")
var config = default_physics_config_3d()
var world = PhysicsWorld3D.create(config)
world.add_dynamic_body(make_node(0), 0.0, 10.0, 0.0, 1.0)
world.add_sphere_collider(make_node(0), 0.5)
step_3d(world, 30)
val pos = world.get_position(make_node(0))
expect(pos.y < 10.0).to_equal(true)
expect(pos.y > -50.0).to_equal(true)
world.destroy()
```

</details>

#### x and z unchanged for vertical drop

- x and z unchanged for vertical drop
   - Expected: math_abs(pos.x - 3.0) < 0.01 is true
   - Expected: math_abs(pos.z - (-2.0)) < 0.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("x and z unchanged for vertical drop")
var config = default_physics_config_3d()
var world = PhysicsWorld3D.create(config)
world.add_dynamic_body(make_node(0), 3.0, 10.0, -2.0, 1.0)
world.add_sphere_collider(make_node(0), 0.5)
step_3d(world, 20)
val pos = world.get_position(make_node(0))
expect(math_abs(pos.x - 3.0) < 0.01).to_equal(true)
expect(math_abs(pos.z - (-2.0)) < 0.01).to_equal(true)
world.destroy()
```

</details>

#### body count correct

- body count correct
   - Expected: world.body_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("body count correct")
var config = default_physics_config_3d()
var world = PhysicsWorld3D.create(config)
world.add_dynamic_body(make_node(0), 0.0, 5.0, 0.0, 1.0)
world.add_sphere_collider(make_node(0), 0.5)
world.add_static_body(make_node(1), 0.0, 0.0, 0.0)
world.add_box_collider(make_node(1), 5.0, 0.5, 5.0)
expect(world.body_count()).to_equal(2)
world.destroy()
```

</details>

#### velocity increases during fall

- velocity increases during fall
   - Expected: vel.y < -0.1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("velocity increases during fall")
var config = default_physics_config_3d()
var world = PhysicsWorld3D.create(config)
world.add_dynamic_body(make_node(0), 0.0, 10.0, 0.0, 1.0)
world.add_sphere_collider(make_node(0), 0.5)
step_3d(world, 10)
val vel = world.get_velocity(make_node(0))
expect(vel.y < -0.1).to_equal(true)
world.destroy()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_3d_smoke_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Physics2 3D Smoke Test.
- Physics2 3D Smoke Test

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `683bfbde62a75bb889d4e1ff370c16c35dee1c90a06bccdefed69018096cafb9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `683bfbde62a75bb889d4e1ff370c16c35dee1c90a06bccdefed69018096cafb9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `683bfbde62a75bb889d4e1ff370c16c35dee1c90a06bccdefed69018096cafb9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/engine/physics_3d_smoke_spec.spl
mirror: doc/06_spec/03_system/engine/physics_3d_smoke_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/engine/physics_3d_smoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/engine/physics_3d_smoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/engine/physics_3d_smoke_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/engine/physics_3d_smoke_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sphere falls under gravity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/physics_3d_smoke_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'x and z unchanged for vertical drop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/physics_3d_smoke_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'body count correct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
