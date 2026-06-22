# Engine3d Texture Specification

> 1. var engine = Engine3D create

<!-- sdn-diagram:id=engine3d_texture_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine3d_texture_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine3d_texture_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine3d_texture_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine3d Texture Specification

## Scenarios

### Engine3D Texture Operations

#### engine construction

#### Engine3D.create creates engine with 320x240

1. var engine = Engine3D create
   - Expected: engine._w equals `320`
   - Expected: engine._h equals `240`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
expect(engine._w).to_equal(320)
expect(engine._h).to_equal(240)
```

</details>

#### load_texture

#### returns handle with correct width and height

1. var engine = Engine3D create
   - Expected: handle.width equals `64`
   - Expected: handle.height equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val pixels: [u32] = [0xFFFFFFFF]
val handle = engine.load_texture(64, 64, pixels)
expect(handle.width).to_equal(64)
expect(handle.height).to_equal(64)
```

</details>

#### returns handle with gpu_id >= -1 in emu

1. var engine = Engine3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val pixels: [u32] = [0xFFFFFFFF]
val handle = engine.load_texture(64, 64, pixels)
expect(handle.gpu_id).to_be_greater_than(-2)
```

</details>

#### load_depth_texture

#### returns handle with format TEX_FMT_DEPTH32_FLOAT

1. var engine = Engine3D create
   - Expected: handle.format equals `TEX_FMT_DEPTH32_FLOAT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val handle = engine.load_depth_texture(128, 128)
expect(handle.format).to_equal(TEX_FMT_DEPTH32_FLOAT)
```

</details>

#### load_cubemap

#### returns handle with depth 6

1. var engine = Engine3D create
   - Expected: handle.depth equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val face: [u32] = [0xFF000000]
val faces: [[u32]] = [face, face, face, face, face, face]
val handle = engine.load_cubemap(64, faces)
expect(handle.depth).to_equal(6)
```

</details>

#### unload_texture

#### after unload resource_pool texture_count decrements

1. var engine = Engine3D create
2. engine unload texture
   - Expected: after equals `before - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val pixels: [u32] = [0xFFFFFFFF]
val handle = engine.load_texture(64, 64, pixels)
val before = engine.resource_pool().texture_count()
engine.unload_texture(handle)
val after = engine.resource_pool().texture_count()
expect(after).to_equal(before - 1)
```

</details>

#### load_shader and unload_shader

#### load_shader returns handle with valid id

1. var engine = Engine3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val handle = engine.load_shader("void main(){}", "void main(){}")
expect(handle.id).to_be_greater_than(0)
```

</details>

#### unload_shader frees the shader

1. var engine = Engine3D create
2. engine unload shader
   - Expected: after equals `before - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val handle = engine.load_shader("void main(){}", "void main(){}")
val before = engine.resource_pool().shader_count()
engine.unload_shader(handle)
val after = engine.resource_pool().shader_count()
expect(after).to_equal(before - 1)
```

</details>

#### load_buffer and unload_buffer

#### load_buffer returns handle with valid id

1. var engine = Engine3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val handle = engine.load_buffer(1024)
expect(handle.id).to_be_greater_than(0)
```

</details>

#### unload_buffer frees the buffer

1. var engine = Engine3D create
2. engine unload buffer
   - Expected: after equals `before - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val handle = engine.load_buffer(1024)
val before = engine.resource_pool().buffer_count()
engine.unload_buffer(handle)
val after = engine.resource_pool().buffer_count()
expect(after).to_equal(before - 1)
```

</details>

#### load_pipeline

#### creates pipeline from shader handle

1. var engine = Engine3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val shader = engine.load_shader("void main(){}", "void main(){}")
val pipeline = engine.load_pipeline(shader, true, 0, 0)
expect(pipeline.id).to_be_greater_than(0)
```

</details>

#### gc_resources

#### after loading and not touching gc removes stale resources

1. var engine = Engine3D create
2. engine load texture
3. engine resource pool
4. engine resource pool
5. engine gc resources
   - Expected: engine.resource_pool().texture_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val pixels: [u32] = [0xFFFFFFFF]
engine.load_texture(32, 32, pixels)
engine.resource_pool().advance_frame()
engine.resource_pool().advance_frame()
engine.gc_resources(1)
expect(engine.resource_pool().texture_count()).to_equal(1)
```

</details>

#### resource_pool total_resource_count

#### matches expected count after operations

1. var engine = Engine3D create
2. engine load texture
3. engine load buffer
   - Expected: engine.resource_pool().total_resource_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val pixels: [u32] = [0xFFFFFFFF]
engine.load_texture(32, 32, pixels)
val shader = engine.load_shader("void main(){}", "void main(){}")
engine.load_buffer(256)
expect(engine.resource_pool().total_resource_count()).to_equal(3)
```

</details>

#### create_texture_ex

#### with TextureDescriptor3D.create_2d returns i32

1. var engine = Engine3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val desc = TextureDescriptor3D.create_2d(64, 64, TEX_FMT_RGBA8_UNORM)
val data: [u8] = []
val id = engine.create_texture_ex(desc, data)
expect(id).to_be_greater_than(-2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/engine3d_texture_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine3D Texture Operations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
