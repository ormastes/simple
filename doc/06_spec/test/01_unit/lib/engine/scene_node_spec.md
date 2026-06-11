# scene_node_spec

> Engine Scene Node — Node2D & NodeStore Tests

<!-- sdn-diagram:id=scene_node_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scene_node_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scene_node_spec -> std
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
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scene_node_spec

Engine Scene Node — Node2D & NodeStore Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/scene_node_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Scene Node — Node2D & NodeStore Tests

Tests node creation, parent/child hierarchy, position, z-index.

## Scenarios

### NodeStore

#### creates a node and retrieves it

1. var store = NodeStore new
   - Expected: node.name equals `player`
   - Expected: "node not found" equals `node found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
val nid = store.create_node("player")
val maybe_node = store.get_node(nid)
if val Some(node) = maybe_node:
    expect(node.name).to_equal("player")
else:
    expect("node not found").to_equal("node found")
```

</details>

#### returns nil for invalid node id

1. var store = NodeStore new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
val invalid = NodeId.invalid()
val result = store.get_node(invalid)
expect(result).to_be_nil
```

</details>

#### tracks node count

1. var store = NodeStore new
   - Expected: store.count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
val a = store.create_node("a")
val b = store.create_node("b")
expect(store.count).to_equal(2)
```

</details>

#### sets parent-child relationship

1. var store = NodeStore new
   - Expected: ok is true
   - Expected: has_child equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
val parent_id = store.create_node("parent")
val child_id = store.create_node("child")
val ok = store.set_parent(child_id, parent_id)
expect(ok).to_equal(true)
# Verify parent's children contain child
val parent_node = store.get_node(parent_id)
if val Some(p) = parent_node:
    val has_child = p.children.len()
    expect(has_child).to_equal(1)
```

</details>

#### destroys a node

1. var store = NodeStore new
   - Expected: removed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
val nid = store.create_node("doomed")
val initial_count = store.count
val removed = store.destroy_node(nid)
expect(removed).to_equal(true)
expect(store.count).to_be_less_than(initial_count)
val gone = store.get_node(nid)
expect(gone).to_be_nil
```

</details>

#### does not duplicate child entries when reparenting to the same parent

1. var store = NodeStore new
   - Expected: store.set_parent(child_id, parent_id) is true
   - Expected: store.set_parent(child_id, parent_id) is true
   - Expected: p.children.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
val parent_id = store.create_node("parent")
val child_id = store.create_node("child")
expect(store.set_parent(child_id, parent_id)).to_equal(true)
expect(store.set_parent(child_id, parent_id)).to_equal(true)
val parent_node = store.get_node(parent_id)
if val Some(p) = parent_node:
    expect(p.children.len()).to_equal(1)
```

</details>

#### rejects self-parenting

1. var store = NodeStore new
   - Expected: store.set_parent(node_id, node_id) is false
   - Expected: n.parent.is_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
val node_id = store.create_node("loop")
expect(store.set_parent(node_id, node_id)).to_equal(false)
val node = store.get_node(node_id)
if val Some(n) = node:
    expect(n.parent.is_valid()).to_equal(false)
```

</details>

#### rejects parent cycles

1. var store = NodeStore new
   - Expected: store.set_parent(child_id, root_id) is true
   - Expected: store.set_parent(grandchild_id, child_id) is true
   - Expected: store.set_parent(root_id, grandchild_id) is false
   - Expected: node.parent.is_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
val root_id = store.create_node("root")
val child_id = store.create_node("child")
val grandchild_id = store.create_node("grandchild")
expect(store.set_parent(child_id, root_id)).to_equal(true)
expect(store.set_parent(grandchild_id, child_id)).to_equal(true)
expect(store.set_parent(root_id, grandchild_id)).to_equal(false)
val root = store.get_node(root_id)
if val Some(node) = root:
    expect(node.parent.is_valid()).to_equal(false)
```

</details>

#### sets node position

1. var store = NodeStore new
2. store set position
   - Expected: n.position.x equals `42.0`
   - Expected: n.position.y equals `99.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
val nid = store.create_node("movable")
val pos = Vec2(x: 42.0, y: 99.0)
store.set_position(nid, pos)
val node = store.get_node(nid)
if val Some(n) = node:
    expect(n.position.x).to_equal(42.0)
    expect(n.position.y).to_equal(99.0)
```

</details>

#### sets z-index for draw ordering

1. var store = NodeStore new
2. store set z index
   - Expected: n.z_index.value equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
val nid = store.create_node("layered")
store.set_z_index(nid, ZIndex(value: 5))
val node = store.get_node(nid)
if val Some(n) = node:
    expect(n.z_index.value).to_equal(5)
```

</details>

### Scene Tree Queries

#### computes world transform for root node

1. var store = NodeStore new
2. store set position
   - Expected: wt.position.x equals `10.0`
   - Expected: wt.position.y equals `20.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
val root_id = store.create_node("root")
store.set_position(root_id, Vec2(x: 10.0, y: 20.0))
val wt = get_world_transform(store, root_id)
expect(wt.position.x).to_equal(10.0)
expect(wt.position.y).to_equal(20.0)
```

</details>

#### computes world transform with parent offset

1. var store = NodeStore new
2. store set position
3. store set position
4. store set parent


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
val parent_id = store.create_node("parent")
val child_id = store.create_node("child")
store.set_position(parent_id, Vec2(x: 100.0, y: 200.0))
store.set_position(child_id, Vec2(x: 10.0, y: 20.0))
store.set_parent(child_id, parent_id)
val wt = get_world_transform(store, child_id)
# World position = parent + child = (110, 220)
val wx_i = wt.position.x * 100.0
val wy_i = wt.position.y * 100.0
expect(wx_i).to_be_greater_than(10999.0)
expect(wx_i).to_be_less_than(11001.0)
expect(wy_i).to_be_greater_than(21999.0)
expect(wy_i).to_be_less_than(22001.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
