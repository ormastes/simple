# Gpu Bridge Specification

> <details>

<!-- sdn-diagram:id=gpu_bridge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_bridge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_bridge_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_bridge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Bridge Specification

## Scenarios

### GpuRenderState

#### creates uninitialized state

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = GpuRenderState.uninitialized()
expect(state.is_initialized).to_equal(false)
expect(state.is_valid()).to_equal(false)
```

</details>

#### initializes with dimensions via Context

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Use constructor syntax to avoid interpreter TorchStream.create() issue
val gpu = Gpu(backend: GpuBackend.None_, device_id: 0, is_initialized: false)
val ctx = Context(backend: GpuBackend.None_, device: gpu, default_stream: nil)
val state = init_gpu_render_state(ctx, 800, 600, 0)
# With GpuBackend.None, handles are 0 but state is initialized
expect(state.is_initialized).to_equal(true)
expect(state.screen_width).to_equal(800)
expect(state.screen_height).to_equal(600)
```

</details>

### flatten_batch_vertices

#### flattens vertices to f64 array

1. var batch = SpriteBatch create
2. batch add quad
   - Expected: verts_data.len() equals `32`
   - Expected: verts_data[0] equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var batch = SpriteBatch.create(0)
val white = EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0)
batch.add_quad(0.0, 0.0, 10.0, 10.0, 0.0, 0.0, 1.0, 1.0, white)
val verts_data = flatten_batch_vertices(batch)
# 4 vertices * 8 floats each = 32 floats
expect(verts_data.len()).to_equal(32)
# First vertex pos_x should be 0.0
expect(verts_data[0]).to_equal(0.0)
```

</details>

### ShaderSource

#### loads builtin 2D shader

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = load_builtin_2d_shader()
expect(source.name).to_equal("builtin_2d")
expect(source.is_valid()).to_equal(true)
expect(source.vertex_code.len()).to_be_greater_than(0)
expect(source.fragment_code.len()).to_be_greater_than(0)
```

</details>

#### loads builtin 3D shader

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = load_builtin_3d_shader()
expect(source.name).to_equal("builtin_3d")
expect(source.is_valid()).to_equal(true)
```

</details>

#### vertex shader contains version directive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = load_builtin_2d_shader()
expect(source.vertex_code).to_contain("#version 450")
```

</details>

#### fragment shader contains texture sampling

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = load_builtin_2d_shader()
expect(source.fragment_code).to_contain("sampler2D")
```

</details>

### ShaderProgram

#### creates invalid program

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prog = ShaderProgram.invalid()
expect(prog.is_valid()).to_equal(false)
expect(prog.is_compiled).to_equal(false)
```

</details>

#### compiles to unlinked program (stub)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = load_builtin_2d_shader()
val prog = create_shader_program(source)
expect(prog.name).to_equal("builtin_2d")
# Stub returns is_compiled=false until real GPU backing
expect(prog.is_compiled).to_equal(false)
```

</details>

### GpuTextureCache

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = GpuTextureCache.create()
expect(cache.count()).to_equal(0)
expect(cache.total_uploads()).to_equal(0)
```

</details>

#### caches and retrieves GPU texture

1. var cache = GpuTextureCache create
2. cache put
   - Expected: cache.count() equals `1`
   - Expected: cache.has(tex_id) is true
   - Expected: t.handle equals `42`
   - Expected: t.width equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = GpuTextureCache.create()
val tex_id = TextureId(raw: RawHandle(index: 1, generation: Generation(value: 1)))
val gpu_tex = GpuTexture(handle: 42, width: 64, height: 64, format: GpuFormat.RGBA8)
cache.put(tex_id, gpu_tex)
expect(cache.count()).to_equal(1)
expect(cache.has(tex_id)).to_equal(true)
val got = cache.get(tex_id)
if val Some(t) = got:
    expect(t.handle).to_equal(42)
    expect(t.width).to_equal(64)
```

</details>

#### returns nil for uncached texture

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = GpuTextureCache.create()
val tex_id = TextureId(raw: RawHandle(index: 99, generation: Generation(value: 1)))
val got = cache.get(tex_id)
expect(got).to_be_nil
```

</details>

#### removes cached texture

1. var cache = GpuTextureCache create
2. cache put
3. cache remove
   - Expected: cache.has(tex_id) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = GpuTextureCache.create()
val tex_id = TextureId(raw: RawHandle(index: 1, generation: Generation(value: 1)))
val gpu_tex = GpuTexture(handle: 10, width: 32, height: 32, format: GpuFormat.RGBA8)
cache.put(tex_id, gpu_tex)
cache.remove(tex_id)
expect(cache.has(tex_id)).to_equal(false)
```

</details>

#### clears all entries

1. var cache = GpuTextureCache create
2. cache put
3. cache put
   - Expected: cache.count() equals `2`
4. cache clear
   - Expected: cache.count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = GpuTextureCache.create()
val t1 = TextureId(raw: RawHandle(index: 1, generation: Generation(value: 1)))
val t2 = TextureId(raw: RawHandle(index: 2, generation: Generation(value: 1)))
cache.put(t1, GpuTexture(handle: 1, width: 8, height: 8, format: GpuFormat.RGBA8))
cache.put(t2, GpuTexture(handle: 2, width: 8, height: 8, format: GpuFormat.RGBA8))
expect(cache.count()).to_equal(2)
cache.clear()
expect(cache.count()).to_equal(0)
```

</details>

#### tracks total uploads

1. var cache = GpuTextureCache create
2. cache put
3. cache put
   - Expected: cache.total_uploads() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = GpuTextureCache.create()
val t1 = TextureId(raw: RawHandle(index: 1, generation: Generation(value: 1)))
cache.put(t1, GpuTexture(handle: 1, width: 8, height: 8, format: GpuFormat.RGBA8))
cache.put(t1, GpuTexture(handle: 2, width: 8, height: 8, format: GpuFormat.RGBA8))
expect(cache.total_uploads()).to_equal(2)
```

</details>

### create_gpu_texture_desc

#### creates RGBA8 sampled descriptor

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = create_gpu_texture_desc(256, 256)
expect(desc.width).to_equal(256)
expect(desc.height).to_equal(256)
# Format is statically RGBA8 from create_gpu_texture_desc
# Enum method calls not supported in interpreter mode
expect(desc.width).to_equal(desc.height)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/gpu_bridge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GpuRenderState
- flatten_batch_vertices
- ShaderSource
- ShaderProgram
- GpuTextureCache
- create_gpu_texture_desc

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
