# Game Engine Component Specification

> Component system with ComponentType enum, Component trait, and ComponentManager.

<!-- sdn-diagram:id=component_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=component_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

component_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=component_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

1. expect ComponentType Transform to string
2. expect ComponentType Render to string
3. expect ComponentType Physics to string
4. expect ComponentType Audio to string
5. expect ComponentType Script to string
6. expect ComponentType Custom to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect ComponentType.Transform.to_string() == "Transform"
expect ComponentType.Render.to_string() == "Render"
expect ComponentType.Physics.to_string() == "Physics"
expect ComponentType.Audio.to_string() == "Audio"
expect ComponentType.Script.to_string() == "Script"
expect ComponentType.Custom.to_string() == "Custom"
```

</details>

#### provides descriptions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = ComponentType.Physics.description()
expect desc == "Physics simulation and collision"
```

</details>

#### checks type categories

1. expect ComponentType Transform is transform
2. expect ComponentType Render is render
3. expect ComponentType Physics is physics


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect ComponentType.Transform.is_transform() == true
expect ComponentType.Render.is_render() == true
expect ComponentType.Physics.is_physics() == true
```

</details>

#### checks visual and simulation

1. expect ComponentType Render is visual
2. expect ComponentType Physics is simulation
3. expect ComponentType Transform is simulation
4. expect ComponentType Render is output
5. expect ComponentType Audio is output


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect ComponentType.Render.is_visual() == true
expect ComponentType.Physics.is_simulation() == true
expect ComponentType.Transform.is_simulation() == true
expect ComponentType.Render.is_output() == true
expect ComponentType.Audio.is_output() == true
```

</details>

### ComponentManager

#### starts empty

1. expect mgr is empty
2. expect mgr count
3. expect mgr has components


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = ComponentManager.create()
expect mgr.is_empty() == true
expect mgr.count() == 0
expect mgr.has_components() == false
```

</details>

#### provides summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
