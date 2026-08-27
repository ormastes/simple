# Physics Layers Specification

> Tests covering Physics2 CollisionFilter, Physics2 CollisionMatrix.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics Layers Specification

## Scenarios

### Physics2 CollisionFilter

#### all vs all collides

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- all vs all collides
   - Expected: a.should_collide(b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all vs all collides")
val a = CollisionFilter.all()
val b = CollisionFilter.all()
expect(a.should_collide(b)).to_equal(true)
```

</details>

#### none vs any no collision

- none vs any no collision
   - Expected: n.should_collide(a) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("none vs any no collision")
val n = CollisionFilter.none()
val a = CollisionFilter.all()
expect(n.should_collide(a)).to_equal(false)
```

</details>

#### same layer collides

- same layer collides
   - Expected: x.should_collide(y) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("same layer collides")
val x = CollisionFilter.with_mask(2, 2)
val y = CollisionFilter.with_mask(2, 2)
expect(x.should_collide(y)).to_equal(true)
```

</details>

#### different exclusive layers no collision

- different exclusive layers no collision
   - Expected: x.should_collide(y) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("different exclusive layers no collision")
val x = CollisionFilter.with_mask(2, 4)
val y = CollisionFilter.with_mask(8, 1)
expect(x.should_collide(y)).to_equal(false)
```

</details>

### Physics2 CollisionMatrix

<details>
<summary>Advanced: matrix disables collision between layers</summary>

#### matrix disables collision between layers

- matrix disables collision between layers
   - Expected: mx.should_collide(fa, fb) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matrix disables collision between layers")
val mx = matrix_with_disabled_24()
val fa = CollisionFilter.with_mask(2, 4)
val fb = CollisionFilter.with_mask(4, 2)
expect(mx.should_collide(fa, fb)).to_equal(false)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_layers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Physics2 CollisionFilter, Physics2 CollisionMatrix.
- Physics2 CollisionFilter
- Physics2 CollisionMatrix

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

- Canonical SPipe generation for source `cd1f13ff6a8a2d6da6e6312be914e7f50ce791e9f90acfb0bd36527534e93df9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cd1f13ff6a8a2d6da6e6312be914e7f50ce791e9f90acfb0bd36527534e93df9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cd1f13ff6a8a2d6da6e6312be914e7f50ce791e9f90acfb0bd36527534e93df9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/engine/physics_layers_spec.spl
mirror: doc/06_spec/03_system/engine/physics_layers_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/engine/physics_layers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/engine/physics_layers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/engine/physics_layers_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all vs all collides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/physics_layers_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'none vs any no collision' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/physics_layers_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'same layer collides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
