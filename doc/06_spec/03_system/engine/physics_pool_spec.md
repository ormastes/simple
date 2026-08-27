# Physics Pool Specification

> Tests covering Physics2 Pool System.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics Pool Specification

## Scenarios

### Physics2 Pool System

#### cue ball moves after impulse

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- cue ball moves after impulse
   - Expected: pos.x > -2.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cue ball moves after impulse")
var world = make_pool_world()
world.apply_impulse(make_node(0), 5.0, 0.0)
step_n(world, 30)
val pos = world.get_position(make_node(0))
expect(pos.x > -2.0).to_equal(true)
world.destroy()
```

</details>

#### positions remain finite after simulation

- positions remain finite after simulation
   - Expected: check_positions_finite(world) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("positions remain finite after simulation")
var world = make_pool_world()
world.apply_impulse(make_node(0), 5.0, 0.3)
step_n(world, 100)
expect(check_positions_finite(world)).to_equal(true)
world.destroy()
```

</details>

#### kinetic energy bounded

- kinetic energy bounded
   - Expected: ke < 50.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("kinetic energy bounded")
var world = make_pool_world()
world.apply_impulse(make_node(0), 5.0, 0.0)
step_n(world, 100)
val ke = get_total_ke(world)
expect(ke < 50.0).to_equal(true)
world.destroy()
```

</details>

#### deterministic across two runs

- deterministic across two runs
   - Expected: r1.0 equals `r2.0`
   - Expected: r1.1 equals `r2.1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("deterministic across two runs")
val r1 = run_deterministic(5.0, 0.1, 80)
val r2 = run_deterministic(5.0, 0.1, 80)
expect(r1.0).to_equal(r2.0)
expect(r1.1).to_equal(r2.1)
```

</details>

#### target ball gets displaced by collision

- target ball gets displaced by collision
   - Expected: after.x > 1.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("target ball gets displaced by collision")
var config = default_physics_config_2d()
config.gravity = Vec2(x: 0.0, y: 0.0)
config.restitution = 0.9
config.backend = PhysicsBackend.CpuScalar
var world = PhysicsWorld2D.create(config)
world.add_dynamic_body(make_node(0), 0.0, 0.0, 1.0)
world.add_circle_collider(make_node(0), 0.5)
world.add_dynamic_body(make_node(1), 0.8, 0.0, 1.0)
world.add_circle_collider(make_node(1), 0.5)
world.apply_impulse(make_node(0), 5.0, 0.0)
step_n(world, 10)
val after = world.get_position(make_node(1))
expect(after.x > 1.0).to_equal(true)
world.destroy()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_pool_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Physics2 Pool System.
- Physics2 Pool System

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

- Canonical SPipe generation for source `36cdbb0e71d72916bc557aae14bad45b51b7080ca6f60007e595669895fd9fd0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `36cdbb0e71d72916bc557aae14bad45b51b7080ca6f60007e595669895fd9fd0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `36cdbb0e71d72916bc557aae14bad45b51b7080ca6f60007e595669895fd9fd0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/engine/physics_pool_spec.spl
mirror: doc/06_spec/03_system/engine/physics_pool_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/engine/physics_pool_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/engine/physics_pool_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/engine/physics_pool_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cue ball moves after impulse' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/physics_pool_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'positions remain finite after simulation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/physics_pool_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'kinetic energy bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
