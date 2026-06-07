# scene_manager_spec

> Engine Scene Manager — SceneManager Tests

<!-- sdn-diagram:id=scene_manager_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scene_manager_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scene_manager_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scene_manager_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scene_manager_spec

Engine Scene Manager — SceneManager Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/scene_manager_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Scene Manager — SceneManager Tests

Tests multi-scene load/unload, additive loading, and active scene switching.

## Scenarios

### SceneManager

#### loads a scene and sets it active

1. var store = NodeStore new
2. var mgr = SceneManager new
   - Expected: handle.name equals `level_1`
   - Expected: handle.root_node.is_valid() is true
   - Expected: mgr.scene_count() equals `1`
   - Expected: mgr.active_scene equals `handle.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
var mgr = SceneManager.new(store)
val handle = mgr.load_scene("level_1")
expect(handle.name).to_equal("level_1")
expect(handle.root_node.is_valid()).to_equal(true)
expect(mgr.scene_count()).to_equal(1)
expect(mgr.active_scene).to_equal(handle.id)
```

</details>

#### unloads a scene

1. var store = NodeStore new
2. var mgr = SceneManager new
   - Expected: removed is true
   - Expected: mgr.scene_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
var mgr = SceneManager.new(store)
val handle = mgr.load_scene("temp")
val removed = mgr.unload_scene(handle.id)
expect(removed).to_equal(true)
expect(mgr.scene_count()).to_equal(0)
```

</details>

#### clears active when unloading the active scene

1. var store = NodeStore new
2. var mgr = SceneManager new
3. mgr unload scene
   - Expected: mgr.active_scene equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
var mgr = SceneManager.new(store)
val handle = mgr.load_scene("main")
mgr.unload_scene(handle.id)
expect(mgr.active_scene).to_equal(-1)
```

</details>

#### returns false when unloading non-existent scene

1. var store = NodeStore new
2. var mgr = SceneManager new
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
var mgr = SceneManager.new(store)
val result = mgr.unload_scene(999)
expect(result).to_equal(false)
```

</details>

#### loads additive scene without changing active

1. var store = NodeStore new
2. var mgr = SceneManager new
   - Expected: mgr.scene_count() equals `2`
   - Expected: mgr.active_scene equals `main_h.id`
   - Expected: ui_h.name equals `ui_overlay`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
var mgr = SceneManager.new(store)
val main_h = mgr.load_scene("main")
val ui_h = mgr.load_additive("ui_overlay")
expect(mgr.scene_count()).to_equal(2)
expect(mgr.active_scene).to_equal(main_h.id)
expect(ui_h.name).to_equal("ui_overlay")
```

</details>

#### switches active scene

1. var store = NodeStore new
2. var mgr = SceneManager new
   - Expected: ok is true
   - Expected: mgr.active_scene equals `h2.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
var mgr = SceneManager.new(store)
val h1 = mgr.load_scene("scene_a")
val h2 = mgr.load_additive("scene_b")
val ok = mgr.set_active(h2.id)
expect(ok).to_equal(true)
expect(mgr.active_scene).to_equal(h2.id)
```

</details>

#### returns false when setting active to unknown id

1. var store = NodeStore new
2. var mgr = SceneManager new
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
var mgr = SceneManager.new(store)
val ok = mgr.set_active(42)
expect(ok).to_equal(false)
```

</details>

#### looks up scene by id

1. var store = NodeStore new
2. var mgr = SceneManager new
   - Expected: all.len() equals `1`
   - Expected: all[0].name equals `findme`
   - Expected: all[0].id equals `h.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
var mgr = SceneManager.new(store)
val h = mgr.load_scene("findme")
val all = mgr.get_all_scenes()
expect(all.len()).to_equal(1)
expect(all[0].name).to_equal("findme")
expect(all[0].id).to_equal(h.id)
```

</details>

#### returns all loaded scenes

1. var store = NodeStore new
2. var mgr = SceneManager new
3. mgr load scene
4. mgr load additive
5. mgr load additive
   - Expected: all.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
var mgr = SceneManager.new(store)
mgr.load_scene("a")
mgr.load_additive("b")
mgr.load_additive("c")
val all = mgr.get_all_scenes()
expect(all.len()).to_equal(3)
```

</details>

#### creates root nodes in the store

1. var store = NodeStore new
2. var mgr = SceneManager new
   - Expected: h.root_node.is_valid() is true
   - Expected: h.name equals `world`
   - Expected: mgr.store.node_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
var mgr = SceneManager.new(store)
val h = mgr.load_scene("world")
# Verify root node was created via handle validity
expect(h.root_node.is_valid()).to_equal(true)
expect(h.name).to_equal("world")
expect(mgr.store.node_count()).to_equal(1)
```

</details>

#### assigns unique ids to scenes

1. var store = NodeStore new
2. var mgr = SceneManager new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore.new()
var mgr = SceneManager.new(store)
val h1 = mgr.load_scene("first")
val h2 = mgr.load_additive("second")
expect(h1.id).to_be_less_than(h2.id)
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
