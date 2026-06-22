# Game Engine SceneNode Specification

> SceneNode trait using Transformd for transform hierarchy.

<!-- sdn-diagram:id=scene_node_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scene_node_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scene_node_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scene_node_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Transformd.identity()
expect(t.position.is_zero()).to_equal(true)
expect(t.rotation.w).to_equal(1.0)
expect(t.scale.x).to_equal(1.0)
```

</details>

#### Transformd supports position, rotation, scale

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
