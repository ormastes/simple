# Game Engine SceneNode Specification

> SceneNode trait using Transformd for transform hierarchy.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game Engine SceneNode Specification

SceneNode trait using Transformd for transform hierarchy.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GE-002 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/scene_node_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
SceneNode trait using Transformd for transform hierarchy.

## Key Concepts
| Concept | Description |
|---------|-------------|
| SceneNode | Trait for scene graph nodes |
| Transformd | f64 transform (position, rotation, scale) |

## Behavior
- SceneNode trait defines transform, hierarchy, naming, visibility
- Uses Transformd instead of tuple-based Transform3D
- Trait-only design (no FFI adapters)

## Scenarios

### SceneNode Transform Integration

#### Transformd works as scene node transform

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Transformd works as scene node transform
   - Expected: t.position.is_zero() is true
   - Expected: t.rotation.w equals `1.0`
   - Expected: t.scale.x equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Transformd works as scene node transform")
val t = Transformd.identity()
expect(t.position.is_zero()).to_equal(true)
expect(t.rotation.w).to_equal(1.0)
expect(t.scale.x).to_equal(1.0)
```

</details>

#### Transformd supports position, rotation, scale

- Transformd supports position, rotation, scale
   - Expected: t.position.x equals `10.0`
   - Expected: t.scale.x equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Transformd supports position, rotation, scale")
val pos = Vec3d(x: 10.0, y: 20.0, z: 30.0)
val rot = Quatd.identity()
val scl = Vec3d(x: 2.0, y: 2.0, z: 2.0)
val t = Transformd(position: pos, rotation: rot, scale: scl)
expect(t.position.x).to_equal(10.0)
expect(t.scale.x).to_equal(2.0)
```

</details>

<details>
<summary>Advanced: Transformd converts to matrix for rendering</summary>

#### Transformd converts to matrix for rendering

- Transformd converts to matrix for rendering
   - Expected: m.data[12] equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Transformd converts to matrix for rendering")
val t = Transformd(position: Vec3d(x: 5.0, y: 0.0, z: 0.0), rotation: Quatd.identity(), scale: Vec3d.one())
val m = t.to_mat4()
# Translation in column 3
expect(m.data[12]).to_equal(5.0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `c99aad289e7f6e5b1865d9bcb1915156cc2e14d8bb27f48c5183d552a04ccb0f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c99aad289e7f6e5b1865d9bcb1915156cc2e14d8bb27f48c5183d552a04ccb0f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c99aad289e7f6e5b1865d9bcb1915156cc2e14d8bb27f48c5183d552a04ccb0f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/usage/scene_node_spec.spl
mirror: doc/06_spec/03_system/feature/usage/scene_node_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/scene_node_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/scene_node_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/scene_node_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/scene_node_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Transformd works as scene node transform' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/scene_node_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Transformd supports position, rotation, scale' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/scene_node_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Transformd converts to matrix for rendering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
