# Physics Stacking Specification

> Tests covering Physics2 Stacking System.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics Stacking Specification

## Scenarios

### Physics2 Stacking System

#### crates settle above floor

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- crates settle above floor
   - Expected: all_above_floor(world, 3) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("crates settle above floor")
var world = make_stack_world(3)
step_n(world, 100)
expect(all_above_floor(world, 3)).to_equal(true)
world.destroy()
```

</details>

#### stack height bounded

- stack height bounded
   - Expected: h < 10.0 is true
   - Expected: h > 0.5 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stack height bounded")
var world = make_stack_world(3)
step_n(world, 100)
val h = max_height(world, 3)
expect(h < 10.0).to_equal(true)
expect(h > 0.5).to_equal(true)
world.destroy()
```

</details>

#### gravity pulls crates down

- gravity pulls crates down
   - Expected: after.y < before.y is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gravity pulls crates down")
var world = make_stack_world(1)
val before = world.get_position(make_node(1))
step_n(world, 20)
val after = world.get_position(make_node(1))
expect(after.y < before.y).to_equal(true)
world.destroy()
```

</details>

#### floor stops falling crate

- floor stops falling crate
   - Expected: pos.y > 0.0 is true
   - Expected: pos.y < 3.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("floor stops falling crate")
var world = make_stack_world(1)
step_n(world, 150)
val pos = world.get_position(make_node(1))
expect(pos.y > 0.0).to_equal(true)
expect(pos.y < 3.0).to_equal(true)
world.destroy()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_stacking_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Physics2 Stacking System.
- Physics2 Stacking System

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

- Canonical SPipe generation for source `9e11003e3707b0bcdd520b2b6d868a149bf924b89cd6f1be7f9d215ae857d109`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9e11003e3707b0bcdd520b2b6d868a149bf924b89cd6f1be7f9d215ae857d109`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9e11003e3707b0bcdd520b2b6d868a149bf924b89cd6f1be7f9d215ae857d109`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/engine/physics_stacking_spec.spl
mirror: doc/06_spec/03_system/engine/physics_stacking_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/engine/physics_stacking_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/engine/physics_stacking_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/engine/physics_stacking_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'crates settle above floor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/physics_stacking_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stack height bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/physics_stacking_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gravity pulls crates down' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
