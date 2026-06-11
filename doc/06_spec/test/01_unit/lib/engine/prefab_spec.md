# prefab_spec

> Engine Prefab System — PrefabTemplate + PrefabStore Tests

<!-- sdn-diagram:id=prefab_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=prefab_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

prefab_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=prefab_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# prefab_spec

Engine Prefab System — PrefabTemplate + PrefabStore Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/prefab_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Prefab System — PrefabTemplate + PrefabStore Tests

Tests prefab template creation, properties, children, registration,
lookup, and instantiation into a NodeStore.

## Scenarios

### PrefabTemplate

#### creates with type and name

1. var tmpl = PrefabTemplate new
   - Expected: tmpl.type_name equals `Sprite`
   - Expected: tmpl.name equals `player`
   - Expected: tmpl.properties.len() equals `0`
   - Expected: tmpl.child_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tmpl = PrefabTemplate.new("Sprite", "player")
expect(tmpl.type_name).to_equal("Sprite")
expect(tmpl.name).to_equal("player")
expect(tmpl.properties.len()).to_equal(0)
expect(tmpl.child_count()).to_equal(0)
```

</details>

#### sets and gets properties

1. var tmpl = PrefabTemplate new
2. tmpl set property
3. tmpl set property
   - Expected: tmpl.properties.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tmpl = PrefabTemplate.new("Sprite", "player")
tmpl.set_property("speed", "10.0")
tmpl.set_property("health", "100")
expect(tmpl.properties.len()).to_equal(2)
```

</details>

#### updates existing property

1. var tmpl = PrefabTemplate new
2. tmpl set property
3. tmpl set property
   - Expected: tmpl.properties.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tmpl = PrefabTemplate.new("Sprite", "player")
tmpl.set_property("speed", "10.0")
tmpl.set_property("speed", "20.0")
expect(tmpl.properties.len()).to_equal(1)
```

</details>

#### adds child templates

1. var tmpl = PrefabTemplate new
2. tmpl add child
   - Expected: tmpl.child_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tmpl = PrefabTemplate.new("Node", "root")
val child = PrefabTemplate.new("Sprite", "arm")
tmpl.add_child(child)
expect(tmpl.child_count()).to_equal(1)
```

</details>

### PrefabStore

#### registers and retrieves prefabs

1. var pstore = PrefabStore new
   - Expected: idx equals `0`
   - Expected: pstore.size() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pstore = PrefabStore.new()
val tmpl = PrefabTemplate.new("Sprite", "player")
val idx = pstore.register(tmpl)
expect(idx).to_equal(0)
expect(pstore.size()).to_equal(1)
```

</details>

#### finds prefab by name

1. var pstore = PrefabStore new
2. pstore register
3. pstore register
   - Expected: p.name equals `sun`
   - Expected: p.type_name equals `Light`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pstore = PrefabStore.new()
pstore.register(PrefabTemplate.new("Sprite", "player"))
pstore.register(PrefabTemplate.new("Light", "sun"))
val found = pstore.find_by_name("sun")
if val Some(p) = found:
    expect(p.name).to_equal("sun")
    expect(p.type_name).to_equal("Light")
```

</details>

#### finds prefabs by type

1. var pstore = PrefabStore new
2. pstore register
3. pstore register
4. pstore register
   - Expected: sprites.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pstore = PrefabStore.new()
pstore.register(PrefabTemplate.new("Sprite", "a"))
pstore.register(PrefabTemplate.new("Light", "b"))
pstore.register(PrefabTemplate.new("Sprite", "c"))
val sprites = pstore.find_by_type("Sprite")
expect(sprites.len()).to_equal(2)
```

</details>

#### returns nil for invalid index

1. var pstore = PrefabStore new
   - Expected: result == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pstore = PrefabStore.new()
val result = pstore.get(99)
expect(result == nil).to_equal(true)
```

</details>

#### instantiates a simple prefab

1. var pstore = PrefabStore new
2. var node store = NodeStore new
   - Expected: node_id.is_valid() is true
   - Expected: node_store.node_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pstore = PrefabStore.new()
val tmpl = PrefabTemplate.new("Sprite", "hero")
val idx = pstore.register(tmpl)
var node_store = NodeStore.new()
val node_id = pstore.instantiate(idx, node_store)
expect(node_id.is_valid()).to_equal(true)
expect(node_store.node_count()).to_equal(1)
```

</details>

#### instantiates prefab with children

1. var pstore = PrefabStore new
2. var tmpl = PrefabTemplate new
3. tmpl add child
4. tmpl add child
5. var node store = NodeStore new
   - Expected: root_id.is_valid() is true
   - Expected: node_store.node_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pstore = PrefabStore.new()
var tmpl = PrefabTemplate.new("Node", "robot")
tmpl.add_child(PrefabTemplate.new("Sprite", "arm_l"))
tmpl.add_child(PrefabTemplate.new("Sprite", "arm_r"))
val idx = pstore.register(tmpl)
var node_store = NodeStore.new()
val root_id = pstore.instantiate(idx, node_store)
expect(root_id.is_valid()).to_equal(true)
expect(node_store.node_count()).to_equal(3)
```

</details>

#### returns invalid id for bad index

1. var pstore = PrefabStore new
2. var node store = NodeStore new
   - Expected: bad_id.is_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pstore = PrefabStore.new()
var node_store = NodeStore.new()
val bad_id = pstore.instantiate(99, node_store)
expect(bad_id.is_valid()).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
