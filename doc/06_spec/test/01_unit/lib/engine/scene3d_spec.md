# scene3d_spec

> Engine Scene3D — NodeStore3D Tests

<!-- sdn-diagram:id=scene3d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scene3d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scene3d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scene3d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scene3d_spec

Engine Scene3D — NodeStore3D Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/scene3d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Scene3D — NodeStore3D Tests

Tests 3D node creation, parent-child relationships,
and world transform computation.

## Scenarios

### NodeStore3D

### creation

#### starts with zero nodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = NodeStore3D.create()
expect(store.node_count()).to_equal(0)
```

</details>

#### creates a node and increments count

1. var store = NodeStore3D create
   - Expected: store.node_count() equals `1`
   - Expected: id.is_valid() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore3D.create()
val id = store.create_node("test")
expect(store.node_count()).to_equal(1)
expect(id.is_valid()).to_equal(true)
```

</details>

#### creates multiple nodes

1. var store = NodeStore3D create
   - Expected: store.node_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore3D.create()
val id1 = store.create_node("node1")
val id2 = store.create_node("node2")
val id3 = store.create_node("node3")
expect(store.node_count()).to_equal(3)
```

</details>

### get_node

#### retrieves created node by id

1. var store = NodeStore3D create
   - Expected: maybe != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore3D.create()
val id = store.create_node("hero")
val maybe = store.get_node(id)
expect(maybe != nil).to_equal(true)
```

</details>

#### node has correct name

1. var store = NodeStore3D create
   - Expected: node.name equals `camera`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore3D.create()
val id = store.create_node("camera")
val maybe = store.get_node(id)
if val Some(node) = maybe:
    expect(node.name).to_equal("camera")
```

</details>

### parent-child

#### sets parent correctly

1. var store = NodeStore3D create
   - Expected: result is true
   - Expected: child.parent.is_valid() is true
   - Expected: parent.children.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore3D.create()
val parent_id = store.create_node("parent")
val child_id = store.create_node("child")
val result = store.set_parent(child_id, parent_id)
expect(result).to_equal(true)

val maybe_child = store.get_node(child_id)
if val Some(child) = maybe_child:
    expect(child.parent.is_valid()).to_equal(true)

val maybe_parent = store.get_node(parent_id)
if val Some(parent) = maybe_parent:
    expect(parent.children.len()).to_equal(1)
```

</details>

### position

#### sets position

1. var store = NodeStore3D create
2. store set position
   - Expected: node.position.x equals `5.0`
   - Expected: node.position.y equals `10.0`
   - Expected: node.position.z equals `15.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore3D.create()
val id = store.create_node("obj")
val pos = Vec3(x: 5.0, y: 10.0, z: 15.0)
store.set_position(id, pos)
val maybe = store.get_node(id)
if val Some(node) = maybe:
    expect(node.position.x).to_equal(5.0)
    expect(node.position.y).to_equal(10.0)
    expect(node.position.z).to_equal(15.0)
```

</details>

### world transform

#### computes world transform for child

1. var store = NodeStore3D create
2. store set position
3. store set position
4. store set parent


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore3D.create()
val parent_id = store.create_node("parent")
val child_id = store.create_node("child")
store.set_position(parent_id, Vec3(x: 100.0, y: 0.0, z: 0.0))
store.set_position(child_id, Vec3(x: 10.0, y: 0.0, z: 0.0))
store.set_parent(child_id, parent_id)

val world = get_world_transform_3d(store, child_id)
val p = world.transform_point(Vec3.zero())
val px_i = p.x * 100.0
expect(px_i).to_be_greater_than(10999.0)
expect(px_i).to_be_less_than(11001.0)
```

</details>

### find_by_name

#### finds node by name

1. var store = NodeStore3D create
   - Expected: found != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore3D.create()
val id = store.create_node("target")
val found = find_by_name_3d(store, "target")
expect(found != nil).to_equal(true)
```

</details>

#### returns nil for missing name

1. var store = NodeStore3D create
2. store create node
   - Expected: found == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore3D.create()
store.create_node("exists")
val found = find_by_name_3d(store, "missing")
expect(found == nil).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
