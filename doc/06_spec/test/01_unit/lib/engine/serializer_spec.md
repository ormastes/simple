# serializer_spec

> Scene Serializer — serialize/deserialize Tests

<!-- sdn-diagram:id=serializer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=serializer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

serializer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=serializer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# serializer_spec

Scene Serializer — serialize/deserialize Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/serializer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Scene Serializer — serialize/deserialize Tests

Tests round-trip serialization of a NodeStore with parent-child relationships.

## Scenarios

### Scene Serializer

#### serializes and deserializes a scene with parent and children

1. var store = NodeStore new
2. store set parent
3. store set parent
4. store set position
5. store set position
6. store set position
7. store set z index
8. store add tag
9. store add tag
   - Expected: restored.node_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
val root_id = store.create_node("root")
val child1_id = store.create_node("child_a")
val child2_id = store.create_node("child_b")
store.set_parent(child1_id, root_id)
store.set_parent(child2_id, root_id)
store.set_position(root_id, Vec2(x: 100.0, y: 200.0))
store.set_position(child1_id, Vec2(x: 10.0, y: 20.0))
store.set_position(child2_id, Vec2(x: 30.0, y: 40.0))
store.set_z_index(root_id, ZIndex(value: 5))
store.add_tag(root_id, "player")
store.add_tag(root_id, "entity")

val sdn = serialize_scene(store)
val restored = deserialize_scene(sdn)

# Verify node count
expect(restored.node_count()).to_equal(3)
```

</details>

#### preserves node names through round-trip

1. var store = NodeStore new
   - Expected: node0.name equals `alpha`
   - Expected: node1.name equals `beta`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
val id0 = store.create_node("alpha")
val id1 = store.create_node("beta")

val sdn = serialize_scene(store)
val restored = deserialize_scene(sdn)

val raw0 = RawHandle.new(0, 1)
val nid0 = NodeId(raw: raw0)
val maybe0 = restored.get_node(nid0)
if val Some(node0) = maybe0:
    expect(node0.name).to_equal("alpha")

val raw1 = RawHandle.new(1, 1)
val nid1 = NodeId(raw: raw1)
val maybe1 = restored.get_node(nid1)
if val Some(node1) = maybe1:
    expect(node1.name).to_equal("beta")
```

</details>

#### preserves positions through round-trip

1. var store = NodeStore new
2. store set position
   - Expected: node0.position.x equals `42.0`
   - Expected: node0.position.y equals `99.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
val id0 = store.create_node("positioned")
store.set_position(id0, Vec2(x: 42.0, y: 99.0))

val sdn = serialize_scene(store)
val restored = deserialize_scene(sdn)

val raw0 = RawHandle.new(0, 1)
val nid0 = NodeId(raw: raw0)
val maybe0 = restored.get_node(nid0)
if val Some(node0) = maybe0:
    expect(node0.position.x).to_equal(42.0)
    expect(node0.position.y).to_equal(99.0)
```

</details>

#### preserves parent relationships through round-trip

1. var store = NodeStore new
2. store set parent
   - Expected: child.parent.is_valid() is true
   - Expected: child.parent.to_index() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
val root_id = store.create_node("parent_node")
val child_id = store.create_node("child_node")
store.set_parent(child_id, root_id)

val sdn = serialize_scene(store)
val restored = deserialize_scene(sdn)

val raw1 = RawHandle.new(1, 1)
val nid1 = NodeId(raw: raw1)
val maybe1 = restored.get_node(nid1)
if val Some(child) = maybe1:
    expect(child.parent.is_valid()).to_equal(true)
    expect(child.parent.to_index()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
