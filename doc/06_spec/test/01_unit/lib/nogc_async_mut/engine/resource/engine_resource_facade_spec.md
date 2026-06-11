# Engine Resource Facade Specification

> <details>

<!-- sdn-diagram:id=engine_resource_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine_resource_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine_resource_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine_resource_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Resource Facade Specification

## Scenarios

### nogc_async_mut engine resource facade

#### re-exports handles, resource enums, manager, and scriptable objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = HandleEntry<text>(value: "asset", generation: 1, ref_count: 1)
expect(entry.generation).to_equal(1)
val arena = HandleArena<text>.new()
expect(arena.is_empty()).to_equal(true)

expect(ResourceState.Loaded.is_loaded()).to_equal(true)
expect(ResourceState.Failed.is_failed()).to_equal(true)
expect(ResourceType.AudioClip.to_text()).to_equal("AudioClip")

val manager = ResourceManager.create("assets")
expect(manager.base_path).to_equal("assets")
expect(manager.audio_clip_count()).to_equal(0)

val field = ScriptableField(name: "speed", value: "12")
expect(field.name).to_equal("speed")
val obj = ScriptableObject.new("Config", "player")
expect(obj.field_count()).to_equal(0)
val store = ScriptableObjectStore.new()
expect(store.count).to_equal(0)
```

</details>

#### re-exports glTF structures and document helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val transform = GltfTransform.identity()
expect(transform.scale.x).to_equal(1.0)
expect(GltfQuat.identity().w).to_equal(1.0)
val pos = GltfVec3(x: 1.0, y: 2.0, z: 3.0)
expect(pos.z).to_equal(3.0)

val mesh = GltfMesh.new("cube")
expect(mesh.vertex_count()).to_equal(0)
val material = GltfMaterial.new("mat")
expect(material.is_metallic()).to_equal(false)
val skin = GltfSkin.new("rig")
expect(skin.bone_count()).to_equal(0)
val anim = GltfAnimation.new("idle")
expect(anim.channel_count()).to_equal(0)
val node = GltfNode.new("root")
expect(node.mesh_index).to_equal(-1)

val doc = GltfDocument.new("scene")
expect(doc.scene_name).to_equal("scene")
expect(doc.mesh_count()).to_equal(0)
expect(doc.has_animations()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/engine/resource/engine_resource_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut engine resource facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
