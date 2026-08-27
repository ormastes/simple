# Physics Asteroids Specification

> Tests covering Physics2 Asteroids System.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics Asteroids Specification

## Scenarios

### Physics2 Asteroids System

#### many bodies simulate without explosion

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- many bodies simulate without explosion
   - Expected: all_bounded is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("many bodies simulate without explosion")
var world = make_asteroid_field(20)
step_n(world, 30)
var all_bounded = true
var i = 0
while i < 20:
    val pos = world.get_position(make_node(i))
    if pos.x < -50.0 or pos.x > 50.0:
        all_bounded = false
    if pos.y < -50.0 or pos.y > 50.0:
        all_bounded = false
    i = i + 1
expect(all_bounded).to_equal(true)
world.destroy()
```

</details>

#### BVH used for many colliders

- BVH used for many colliders
   - Expected: world.colliders.count > 4 is true
   - Expected: world.use_bvh is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BVH used for many colliders")
var world = make_asteroid_field(10)
expect(world.colliders.count > 4).to_equal(true)
expect(world.use_bvh).to_equal(true)
world.destroy()
```

</details>

#### raycast hits nearest body

- raycast hits nearest body
   - Expected: hit.has_hit is true
   - Expected: hit.distance < 5.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("raycast hits nearest body")
var config = default_physics_config_2d()
config.gravity = Vec2(x: 0.0, y: 0.0)
var world = PhysicsWorld2D.create(config)
world.add_static_body(make_node(0), 5.0, 0.0)
world.add_circle_collider(make_node(0), 1.0)
world.add_static_body(make_node(1), 10.0, 0.0)
world.add_circle_collider(make_node(1), 1.0)
val hit = raycast_2d(0.0, 0.0, 1.0, 0.0, 100.0, world.bodies, world.colliders)
expect(hit.has_hit).to_equal(true)
expect(hit.distance < 5.0).to_equal(true)
world.destroy()
```

</details>

#### overlap query finds bodies in radius

- overlap query finds bodies in radius
   - Expected: results.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("overlap query finds bodies in radius")
var config = default_physics_config_2d()
config.gravity = Vec2(x: 0.0, y: 0.0)
var world = PhysicsWorld2D.create(config)
world.add_static_body(make_node(0), 2.0, 0.0)
world.add_circle_collider(make_node(0), 0.5)
world.add_static_body(make_node(1), 10.0, 0.0)
world.add_circle_collider(make_node(1), 0.5)
val results = circle_overlap_2d(0.0, 0.0, 3.0, world.bodies, world.colliders)
expect(results.len() > 0).to_equal(true)
world.destroy()
```

</details>

#### body count tracks correctly

- body count tracks correctly
   - Expected: world.body_count() equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("body count tracks correctly")
var world = make_asteroid_field(15)
expect(world.body_count()).to_equal(15)
world.destroy()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_asteroids_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Physics2 Asteroids System.
- Physics2 Asteroids System

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `e74bc5d528ade8c5cd4221c997f56c348dae286e6f26c00acf41679a30ae7abe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e74bc5d528ade8c5cd4221c997f56c348dae286e6f26c00acf41679a30ae7abe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e74bc5d528ade8c5cd4221c997f56c348dae286e6f26c00acf41679a30ae7abe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/engine/physics_asteroids_spec.spl
mirror: doc/06_spec/03_system/engine/physics_asteroids_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/engine/physics_asteroids_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/engine/physics_asteroids_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/engine/physics_asteroids_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/engine/physics_asteroids_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'many bodies simulate without explosion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/physics_asteroids_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'BVH used for many colliders' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/physics_asteroids_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'raycast hits nearest body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
