# Physics Breakout Specification

> Tests covering Physics2 Breakout System.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics Breakout Specification

## Scenarios

### Physics2 Breakout System

#### ball moves after launch

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ball moves after launch
   - Expected: pos.y > 1.5 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ball moves after launch")
var world = make_breakout_world()
world.apply_impulse(make_node(0), 2.0, 4.0)
step_n(world, 20)
val pos = world.get_position(make_node(0))
expect(pos.y > 1.5).to_equal(true)
world.destroy()
```

</details>

#### ball stays within world bounds

- ball stays within world bounds
   - Expected: pos.x > -6.0 is true
   - Expected: pos.x < 6.0 is true
   - Expected: pos.y < 8.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ball stays within world bounds")
var world = make_breakout_world()
world.apply_impulse(make_node(0), 3.0, 4.0)
step_n(world, 80)
val pos = world.get_position(make_node(0))
expect(pos.x > -6.0).to_equal(true)
expect(pos.x < 6.0).to_equal(true)
expect(pos.y < 8.0).to_equal(true)
world.destroy()
```

</details>

#### ball speed approximately preserved

- ball speed approximately preserved
   - Expected: speed_after > 1.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ball speed approximately preserved")
var world = make_breakout_world()
world.apply_impulse(make_node(0), 0.5, 4.0)
step_n(world, 30)
val speed_after = get_speed(world)
expect(speed_after > 1.0).to_equal(true)
world.destroy()
```

</details>

#### BVH active with many colliders

- BVH active with many colliders
   - Expected: world.colliders.count > 4 is true
   - Expected: world.use_bvh is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BVH active with many colliders")
var world = make_breakout_world()
expect(world.colliders.count > 4).to_equal(true)
expect(world.use_bvh).to_equal(true)
world.destroy()
```

</details>

#### deterministic simulation

- deterministic simulation
   - Expected: p1.x equals `p2.x`
   - Expected: p1.y equals `p2.y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("deterministic simulation")
var config = default_physics_config_2d()
config.gravity = Vec2(x: 0.0, y: 0.0)
config.restitution = 1.0
config.friction = 0.0
var w1 = PhysicsWorld2D.create(config)
w1.add_dynamic_body(make_node(0), 0.0, 1.0, 1.0)
w1.add_circle_collider(make_node(0), 0.3)
w1.add_static_body(make_node(100), 0.0, 5.0)
w1.add_box_collider(make_node(100), 3.0, 0.5)
w1.apply_impulse(make_node(0), 1.0, 4.0)
step_n(w1, 50)
val p1 = w1.get_position(make_node(0))
w1.destroy()
var config2 = default_physics_config_2d()
config2.gravity = Vec2(x: 0.0, y: 0.0)
config2.restitution = 1.0
config2.friction = 0.0
var w2 = PhysicsWorld2D.create(config2)
w2.add_dynamic_body(make_node(0), 0.0, 1.0, 1.0)
w2.add_circle_collider(make_node(0), 0.3)
w2.add_static_body(make_node(100), 0.0, 5.0)
w2.add_box_collider(make_node(100), 3.0, 0.5)
w2.apply_impulse(make_node(0), 1.0, 4.0)
step_n(w2, 50)
val p2 = w2.get_position(make_node(0))
w2.destroy()
expect(p1.x).to_equal(p2.x)
expect(p1.y).to_equal(p2.y)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_breakout_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Physics2 Breakout System.
- Physics2 Breakout System

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

- Canonical SPipe generation for source `f5de326e33e344c53b017f023aa8d885a754e7c70a71b7d1b90d768fb73b314f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f5de326e33e344c53b017f023aa8d885a754e7c70a71b7d1b90d768fb73b314f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f5de326e33e344c53b017f023aa8d885a754e7c70a71b7d1b90d768fb73b314f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/engine/physics_breakout_spec.spl
mirror: doc/06_spec/03_system/engine/physics_breakout_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/engine/physics_breakout_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/engine/physics_breakout_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/engine/physics_breakout_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ball moves after launch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/physics_breakout_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ball stays within world bounds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/physics_breakout_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ball speed approximately preserved' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
