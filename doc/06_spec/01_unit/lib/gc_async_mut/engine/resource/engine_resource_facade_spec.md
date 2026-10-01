# Engine Resource Facade Specification

> Tests covering gc_async_mut engine resource facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Resource Facade Specification

## Scenarios

### gc_async_mut engine resource facade

#### re-exports handles, resource enums, manager, and scriptable objects

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports handles, resource enums, manager, and scriptable objects
   - Expected: entry.generation equals `1`
   - Expected: arena.is_empty() is true
   - Expected: ResourceState.Loaded.is_loaded() is true
   - Expected: ResourceState.Failed.is_failed() is true
   - Expected: ResourceType.AudioClip.to_text() equals `AudioClip`
   - Expected: manager.base_path equals `assets`
   - Expected: manager.audio_clip_count() equals `0`
   - Expected: field.name equals `speed`
   - Expected: obj.field_count() equals `0`
   - Expected: store.count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports handles, resource enums, manager, and scriptable objects")
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

- re-exports glTF structures and document helpers
   - Expected: transform.scale.x equals `1.0`
   - Expected: GltfQuat.identity().w equals `1.0`
   - Expected: pos.z equals `3.0`
   - Expected: mesh.vertex_count() equals `0`
   - Expected: material.is_metallic() is false
   - Expected: skin.bone_count() equals `0`
   - Expected: anim.channel_count() equals `0`
   - Expected: node.mesh_index equals `-1`
   - Expected: doc.scene_name equals `scene`
   - Expected: doc.mesh_count() equals `0`
   - Expected: doc.has_animations() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports glTF structures and document helpers")
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
| Source | `test/01_unit/lib/gc_async_mut/engine/resource/engine_resource_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut engine resource facade.
- gc_async_mut engine resource facade

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

- Canonical SPipe generation for source `4dc6ae22e3bee27baf8181e2f390f3d2ce09354e05e49bcc7e468a2cc525c875`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4dc6ae22e3bee27baf8181e2f390f3d2ce09354e05e49bcc7e468a2cc525c875`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4dc6ae22e3bee27baf8181e2f390f3d2ce09354e05e49bcc7e468a2cc525c875`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/engine/resource/engine_resource_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/engine/resource/engine_resource_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/engine/resource/engine_resource_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/engine/resource/engine_resource_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/engine/resource/engine_resource_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/engine/resource/engine_resource_facade_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports handles, resource enums, manager, and scriptable objects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/engine/resource/engine_resource_facade_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports glTF structures and document helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
