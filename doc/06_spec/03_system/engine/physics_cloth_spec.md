# Physics Cloth Specification

> Tests covering Physics2 XPBD Cloth System.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics Cloth Specification

## Scenarios

### Physics2 XPBD Cloth System

#### cloth sags under gravity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- cloth sags under gravity
   - Expected: avg_y < -1.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cloth sags under gravity")
var world = make_cloth()
step_cloth(world, 80)
val avg_y = get_bottom_row_avg_y(world)
expect(avg_y < -1.0).to_equal(true)
```

</details>

#### top row stays fixed

- top row stays fixed
   - Expected: fixed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("top row stays fixed")
var world = make_cloth()
step_cloth(world, 60)
val fixed = check_top_row_fixed(world)
expect(fixed).to_equal(true)
```

</details>

#### all particles bounded

- all particles bounded
   - Expected: bounded is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all particles bounded")
var world = make_cloth()
step_cloth(world, 100)
val bounded = check_all_bounded(world)
expect(bounded).to_equal(true)
```

</details>

#### cloth width preserved

- cloth width preserved
   - Expected: width > 2.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cloth width preserved")
var world = make_cloth()
step_cloth(world, 60)
val min_x = get_min_x(world)
val max_x = get_max_x(world)
val width = max_x - min_x
expect(width > 2.0).to_equal(true)
```

</details>

#### constraint convergence

- constraint convergence
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("constraint convergence")
var world = make_cloth()
step_cloth(world, 100)
val ok = check_constraints_reasonable(world)
expect(ok).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_cloth_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Physics2 XPBD Cloth System.
- Physics2 XPBD Cloth System

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

- Canonical SPipe generation for source `1d45abefc2b3013ed675d8ddfe0dd866bcab291aa8e4ebf70f531b4d41f96f88`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1d45abefc2b3013ed675d8ddfe0dd866bcab291aa8e4ebf70f531b4d41f96f88`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1d45abefc2b3013ed675d8ddfe0dd866bcab291aa8e4ebf70f531b4d41f96f88`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/engine/physics_cloth_spec.spl
mirror: doc/06_spec/03_system/engine/physics_cloth_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/engine/physics_cloth_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/engine/physics_cloth_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/engine/physics_cloth_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cloth sags under gravity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/physics_cloth_spec.spl:141:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'top row stays fixed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/physics_cloth_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all particles bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
