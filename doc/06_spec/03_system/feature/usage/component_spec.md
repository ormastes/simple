# Game Engine Component Specification

> Component system with ComponentType enum, Component trait, and ComponentManager.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game Engine Component Specification

Component system with ComponentType enum, Component trait, and ComponentManager.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GE-001 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/component_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Component system with ComponentType enum, Component trait, and ComponentManager.

## Key Concepts
| Concept | Description |
|---------|-------------|
| ComponentType | Enum of standard component categories |
| Component | Trait for component lifecycle |
| ComponentManager | Manages components on an entity |

## Behavior
- ComponentType provides is_* helpers and descriptions
- ComponentManager supports add, remove, query by type
- Trait-only design (no FFI adapters)

## Scenarios

### ComponentType

#### converts to string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- converts to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("converts to string")
expect ComponentType.Transform.to_string() == "Transform"
expect ComponentType.Render.to_string() == "Render"
expect ComponentType.Physics.to_string() == "Physics"
expect ComponentType.Audio.to_string() == "Audio"
expect ComponentType.Script.to_string() == "Script"
expect ComponentType.Custom.to_string() == "Custom"
```

</details>

#### provides descriptions

- provides descriptions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("provides descriptions")
val desc = ComponentType.Physics.description()
expect desc == "Physics simulation and collision"
```

</details>

#### checks type categories

- checks type categories


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks type categories")
expect ComponentType.Transform.is_transform() == true
expect ComponentType.Render.is_render() == true
expect ComponentType.Physics.is_physics() == true
```

</details>

#### checks visual and simulation

- checks visual and simulation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks visual and simulation")
expect ComponentType.Render.is_visual() == true
expect ComponentType.Physics.is_simulation() == true
expect ComponentType.Transform.is_simulation() == true
expect ComponentType.Render.is_output() == true
expect ComponentType.Audio.is_output() == true
```

</details>

### ComponentManager

#### starts empty

- starts empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("starts empty")
val mgr = ComponentManager.create()
expect mgr.is_empty() == true
expect mgr.count() == 0
expect mgr.has_components() == false
```

</details>

#### provides summary

- provides summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("provides summary")
val mgr = ComponentManager.create()
val s = mgr.summary()
expect s == "ComponentManager: 0 components, 0 enabled, 0 initialized"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `4b4b08b5dad92b7b56af91c08b6e1a6ccf8eb83e290c6d34fb8bb858e18123df`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4b4b08b5dad92b7b56af91c08b6e1a6ccf8eb83e290c6d34fb8bb858e18123df`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4b4b08b5dad92b7b56af91c08b6e1a6ccf8eb83e290c6d34fb8bb858e18123df`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/component_spec.spl
mirror: doc/06_spec/03_system/feature/usage/component_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/component_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/component_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/component_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/component_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provides descriptions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/component_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks type categories' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
