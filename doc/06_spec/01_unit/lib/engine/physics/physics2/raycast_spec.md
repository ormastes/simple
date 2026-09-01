# Raycast Specification

> Tests covering Raycast2D.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Raycast Specification

## Scenarios

### Raycast2D

#### hits a box collider

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- hits a box collider
   - Expected: hit.has_hit is true
   - Expected: hit.distance > 3.5 is true
   - Expected: hit.distance < 4.5 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hits a box collider")
val config = default_physics_config_2d()
var world = PhysicsWorld2D.create(config)
val node = make_node(1)
world.add_static_body(node, 5.0, 0.0)
world.add_box_collider(node, 1.0, 1.0)
val hit = raycast_2d(0.0, 0.0, 1.0, 0.0, 100.0, world.bodies, world.colliders)
expect(hit.has_hit).to_equal(true)
expect(hit.distance > 3.5).to_equal(true)
expect(hit.distance < 4.5).to_equal(true)
world.destroy()
```

</details>

#### misses when ray points away

- misses when ray points away
   - Expected: hit.has_hit is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("misses when ray points away")
val config = default_physics_config_2d()
var world = PhysicsWorld2D.create(config)
val node = make_node(1)
world.add_static_body(node, 5.0, 0.0)
world.add_box_collider(node, 1.0, 1.0)
val hit = raycast_2d(0.0, 0.0, -1.0, 0.0, 100.0, world.bodies, world.colliders)
expect(hit.has_hit).to_equal(false)
world.destroy()
```

</details>

#### hits circle collider

- hits circle collider
   - Expected: hit.has_hit is true
   - Expected: hit.distance > 3.5 is true
   - Expected: hit.distance < 4.5 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hits circle collider")
val config = default_physics_config_2d()
var world = PhysicsWorld2D.create(config)
val node = make_node(1)
world.add_static_body(node, 0.0, 5.0)
world.add_circle_collider(node, 1.0)
val hit = raycast_2d(0.0, 0.0, 0.0, 1.0, 100.0, world.bodies, world.colliders)
expect(hit.has_hit).to_equal(true)
expect(hit.distance > 3.5).to_equal(true)
expect(hit.distance < 4.5).to_equal(true)
world.destroy()
```

</details>

#### returns closest hit

- returns closest hit
   - Expected: hit.has_hit is true
   - Expected: hit.distance < 6.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns closest hit")
val config = default_physics_config_2d()
var world = PhysicsWorld2D.create(config)
world.add_static_body(make_node(1), 5.0, 0.0)
world.add_box_collider(make_node(1), 0.5, 0.5)
world.add_static_body(make_node(2), 10.0, 0.0)
world.add_box_collider(make_node(2), 0.5, 0.5)
val hit = raycast_2d(0.0, 0.0, 1.0, 0.0, 100.0, world.bodies, world.colliders)
expect(hit.has_hit).to_equal(true)
expect(hit.distance < 6.0).to_equal(true)
world.destroy()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/physics/physics2/raycast_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Raycast2D.
- Raycast2D

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d6b00f4c24d374e3d3ee355c039142edcd70d4be09d3b8b443e31045f6800e29`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d6b00f4c24d374e3d3ee355c039142edcd70d4be09d3b8b443e31045f6800e29`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d6b00f4c24d374e3d3ee355c039142edcd70d4be09d3b8b443e31045f6800e29`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/engine/physics/physics2/raycast_spec.spl
mirror: doc/06_spec/01_unit/lib/engine/physics/physics2/raycast_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/engine/physics/physics2/raycast_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/engine/physics/physics2/raycast_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/engine/physics/physics2/raycast_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hits a box collider' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/engine/physics/physics2/raycast_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'misses when ray points away' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/engine/physics/physics2/raycast_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hits circle collider' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
