# Engine Scene Facade Specification

> <details>

<!-- sdn-diagram:id=engine_scene_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine_scene_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine_scene_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine_scene_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Scene Facade Specification

## Scenarios

### nogc_async_mut engine scene facade

#### re-exports 2D node and tree surfaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id = NodeId(raw: RawHandle(index: 1, generation: Generation(value: 1)))
val node = Node2D.create(id, "player")
expect(node.name).to_equal("player")
expect(node.get_local_transform().position.x).to_equal(0.0)

val store = NodeStore.new()
expect(get_root_nodes(store).len()).to_equal(0)
expect(get_world_position(store, id).x).to_equal(0.0)
```

</details>

#### re-exports serializer, scene manager, prefab, and 3D surfaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = NodeStore.new()
expect(serialize_scene(store)).to_equal("")
expect(deserialize_scene("").count).to_equal(0)

val handle = SceneHandle(id: 7, name: "level", root_node: NodeId.invalid())
expect(handle.name).to_equal("level")
val manager = SceneManager.new(store)
expect(manager.active_scene).to_equal(-1)

val prop = PrefabProperty(name: "speed", value: "12")
expect(prop.value).to_equal("12")
val prefab_template = PrefabTemplate.new("Sprite", "hero")
expect(prefab_template.type_name).to_equal("Sprite")
val prefab_store = PrefabStore.new()
expect(prefab_store.size()).to_equal(0)

val id = NodeId(raw: RawHandle(index: 2, generation: Generation(value: 1)))
val node3d = Node3D.create(id, "camera")
expect(node3d.get_transform().position.x).to_equal(0.0)
val store3d = NodeStore3D.create()
expect(store3d.count).to_equal(0)
expect(find_by_name_3d(store3d, "missing")).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/engine/scene/engine_scene_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut engine scene facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
