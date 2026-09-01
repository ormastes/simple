# Engine Scene Facade Specification

> Tests covering gc_async_mut engine scene facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Scene Facade Specification

## Scenarios

### gc_async_mut engine scene facade

#### re-exports 2D node and tree surfaces

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports 2D node and tree surfaces
   - Expected: node.name equals `player`
   - Expected: node.get_local_transform().position.x equals `0.0`
   - Expected: get_root_nodes(store).len() equals `0`
   - Expected: get_world_position(store, id).x equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports 2D node and tree surfaces")
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

- re-exports serializer, scene manager, prefab, and 3D surfaces
   - Expected: serialize_scene(store) equals ``
   - Expected: deserialize_scene("").count equals `0`
   - Expected: handle.name equals `level`
   - Expected: manager.active_scene equals `-1`
   - Expected: prop.value equals `12`
   - Expected: prefab_template.type_name equals `Sprite`
   - Expected: prefab_store.size() equals `0`
   - Expected: node3d.get_transform().position.x equals `0.0`
   - Expected: store3d.count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports serializer, scene manager, prefab, and 3D surfaces")
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
| Source | `test/01_unit/lib/gc_async_mut/engine/scene/engine_scene_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut engine scene facade.
- gc_async_mut engine scene facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5684ca4795aadf5eb4446705b8e75729c6bb37225daeda7991c4930eb1ff9d7b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5684ca4795aadf5eb4446705b8e75729c6bb37225daeda7991c4930eb1ff9d7b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5684ca4795aadf5eb4446705b8e75729c6bb37225daeda7991c4930eb1ff9d7b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/engine/scene/engine_scene_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/engine/scene/engine_scene_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/engine/scene/engine_scene_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/engine/scene/engine_scene_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/engine/scene/engine_scene_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/engine/scene/engine_scene_facade_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports 2D node and tree surfaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/engine/scene/engine_scene_facade_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports serializer, scene manager, prefab, and 3D surfaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
