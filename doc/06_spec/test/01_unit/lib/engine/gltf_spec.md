# gltf_spec

> glTF Asset Import — Type and Document Tests

<!-- sdn-diagram:id=gltf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gltf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gltf_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gltf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gltf_spec

glTF Asset Import — Type and Document Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/gltf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

glTF Asset Import — Type and Document Tests

Tests GltfVec3, GltfQuat, GltfTransform, GltfMesh, GltfMaterial,
GltfSkin, GltfAnimation, GltfNode, and GltfDocument.

## Scenarios

### GltfQuat

#### creates identity quaternion

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = GltfQuat.identity()
expect(q.x).to_equal(0.0)
expect(q.y).to_equal(0.0)
expect(q.z).to_equal(0.0)
expect(q.w).to_equal(1.0)
```

</details>

### GltfTransform

#### creates identity transform

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = GltfTransform.identity()
expect(t.translation.x).to_equal(0.0)
expect(t.translation.y).to_equal(0.0)
expect(t.translation.z).to_equal(0.0)
expect(t.rotation.w).to_equal(1.0)
expect(t.scale.x).to_equal(1.0)
expect(t.scale.y).to_equal(1.0)
expect(t.scale.z).to_equal(1.0)
```

</details>

### GltfMesh

#### starts empty

1. var mesh = GltfMesh new
   - Expected: mesh.name equals `cube`
   - Expected: mesh.vertex_count() equals `0`
   - Expected: mesh.index_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mesh = GltfMesh.new("cube")
expect(mesh.name).to_equal("cube")
expect(mesh.vertex_count()).to_equal(0)
expect(mesh.index_count()).to_equal(0)
```

</details>

#### adds vertices and indices

1. var mesh = GltfMesh new
2. mesh add vertex
3. mesh add vertex
4. mesh add vertex
5. mesh add index
6. mesh add index
7. mesh add index
   - Expected: mesh.vertex_count() equals `3`
   - Expected: mesh.index_count() equals `3`
   - Expected: mesh.triangle_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mesh = GltfMesh.new("tri")
mesh.add_vertex(0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0)
mesh.add_vertex(1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 1.0, 0.0)
mesh.add_vertex(0.0, 1.0, 0.0, 0.0, 1.0, 0.0, 0.0, 1.0)
mesh.add_index(0)
mesh.add_index(1)
mesh.add_index(2)
expect(mesh.vertex_count()).to_equal(3)
expect(mesh.index_count()).to_equal(3)
expect(mesh.triangle_count()).to_equal(1)
```

</details>

### GltfMaterial

#### has correct defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mat = GltfMaterial.new("default")
expect(mat.name).to_equal("default")
expect(mat.base_color_r).to_equal(1.0)
expect(mat.base_color_g).to_equal(1.0)
expect(mat.base_color_b).to_equal(1.0)
expect(mat.base_color_a).to_equal(1.0)
expect(mat.metallic).to_equal(0.0)
expect(mat.roughness).to_equal(0.5)
expect(mat.emissive_r).to_equal(0.0)
expect(mat.texture_path).to_equal("")
```

</details>

#### detects metallic materials

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val non_metal = GltfMaterial.new("plastic")
expect(non_metal.is_metallic()).to_equal(false)
val metal = GltfMaterial(
    name: "steel",
    base_color_r: 0.8, base_color_g: 0.8, base_color_b: 0.8, base_color_a: 1.0,
    metallic: 0.9, roughness: 0.3,
    emissive_r: 0.0, emissive_g: 0.0, emissive_b: 0.0,
    texture_path: ""
)
expect(metal.is_metallic()).to_equal(true)
```

</details>

### GltfSkin

#### starts empty

1. var skin = GltfSkin new
   - Expected: skin.name equals `armature`
   - Expected: skin.bone_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var skin = GltfSkin.new("armature")
expect(skin.name).to_equal("armature")
expect(skin.bone_count()).to_equal(0)
```

</details>

#### adds bones and returns indices

1. var skin = GltfSkin new
   - Expected: root_idx equals `0`
   - Expected: child_idx equals `1`
   - Expected: skin.bone_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var skin = GltfSkin.new("skeleton")
val root_idx = skin.add_bone("root", -1, GltfTransform.identity())
val child_idx = skin.add_bone("spine", 0, GltfTransform.identity())
expect(root_idx).to_equal(0)
expect(child_idx).to_equal(1)
expect(skin.bone_count()).to_equal(2)
```

</details>

#### finds bones by name

1. var skin = GltfSkin new
2. skin add bone
3. skin add bone
4. skin add bone
   - Expected: skin.find_bone("leg_r") equals `2`
   - Expected: skin.find_bone("missing") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var skin = GltfSkin.new("rig")
skin.add_bone("hip", -1, GltfTransform.identity())
skin.add_bone("leg_l", 0, GltfTransform.identity())
skin.add_bone("leg_r", 0, GltfTransform.identity())
expect(skin.find_bone("leg_r")).to_equal(2)
expect(skin.find_bone("missing")).to_equal(-1)
```

</details>

### GltfAnimation

#### starts empty

1. var anim = GltfAnimation new
   - Expected: anim.name equals `walk`
   - Expected: anim.channel_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var anim = GltfAnimation.new("walk")
expect(anim.name).to_equal("walk")
expect(anim.channel_count()).to_equal(0)
```

</details>

#### adds channels

1. var anim = GltfAnimation new
2. anim add channel
   - Expected: anim.channel_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var anim = GltfAnimation.new("run")
val ch = GltfAnimChannel(
    bone_index: 0,
    property: "translation",
    times: [0.0, 0.5, 1.0],
    values: [0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0]
)
anim.add_channel(ch)
expect(anim.channel_count()).to_equal(1)
```

</details>

### GltfNode

#### starts with defaults

1. var node = GltfNode new
   - Expected: node.name equals `scene_root`
   - Expected: node.mesh_index equals `-1`
   - Expected: node.skin_index equals `-1`
   - Expected: node.transform.scale.x equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = GltfNode.new("scene_root")
expect(node.name).to_equal("scene_root")
expect(node.mesh_index).to_equal(-1)
expect(node.skin_index).to_equal(-1)
expect(node.transform.scale.x).to_equal(1.0)
```

</details>

### GltfDocument

#### starts empty

1. var doc = GltfDocument new
   - Expected: doc.scene_name equals `test_scene`
   - Expected: doc.mesh_count() equals `0`
   - Expected: doc.material_count() equals `0`
   - Expected: doc.node_count() equals `0`
   - Expected: doc.has_animations() is false
   - Expected: doc.has_skins() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var doc = GltfDocument.new("test_scene")
expect(doc.scene_name).to_equal("test_scene")
expect(doc.mesh_count()).to_equal(0)
expect(doc.material_count()).to_equal(0)
expect(doc.node_count()).to_equal(0)
expect(doc.has_animations()).to_equal(false)
expect(doc.has_skins()).to_equal(false)
```

</details>

#### adds and retrieves meshes

1. var doc = GltfDocument new
2. var mesh = GltfMesh new
3. mesh add vertex
   - Expected: idx equals `0`
   - Expected: doc.mesh_count() equals `1`
   - Expected: m.name equals `cube`
   - Expected: m.vertex_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var doc = GltfDocument.new("scene")
var mesh = GltfMesh.new("cube")
mesh.add_vertex(0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0)
val idx = doc.add_mesh(mesh)
expect(idx).to_equal(0)
expect(doc.mesh_count()).to_equal(1)
val retrieved = doc.get_mesh(0)
if val Some(m) = retrieved:
    expect(m.name).to_equal("cube")
    expect(m.vertex_count()).to_equal(1)
```

</details>

#### adds and retrieves materials

1. var doc = GltfDocument new
   - Expected: idx equals `0`
   - Expected: doc.material_count() equals `1`
   - Expected: m.name equals `wood`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var doc = GltfDocument.new("scene")
val mat = GltfMaterial.new("wood")
val idx = doc.add_material(mat)
expect(idx).to_equal(0)
expect(doc.material_count()).to_equal(1)
val retrieved = doc.get_material(0)
if val Some(m) = retrieved:
    expect(m.name).to_equal("wood")
```

</details>

#### tracks skins and animations

1. var doc = GltfDocument new
2. var skin = GltfSkin new
3. skin add bone
4. doc add skin
   - Expected: doc.has_skins() is true
5. var anim = GltfAnimation new
6. doc add animation
   - Expected: doc.has_animations() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var doc = GltfDocument.new("character")
var skin = GltfSkin.new("body")
skin.add_bone("root", -1, GltfTransform.identity())
doc.add_skin(skin)
expect(doc.has_skins()).to_equal(true)

var anim = GltfAnimation.new("idle")
doc.add_animation(anim)
expect(doc.has_animations()).to_equal(true)
```

</details>

#### adds nodes

1. var doc = GltfDocument new
2. var node = GltfNode new
   - Expected: idx equals `0`
   - Expected: doc.node_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var doc = GltfDocument.new("scene")
var node = GltfNode.new("root")
val idx = doc.add_node(node)
expect(idx).to_equal(0)
expect(doc.node_count()).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
