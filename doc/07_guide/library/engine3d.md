# 3D Engine Library Guide

Covers the `std.gpu.engine3d` module: backend selection, geometry, materials, lighting, camera, textures, resource management, shaders, shadows, post-processing, render passes, and compute.

---

## Getting Started

Import `Engine3D` from `std.gpu.engine3d.engine`:

```simple
use std.gpu.engine3d.engine.{Engine3D}
use std.gpu.engine3d.types3d.{Vertex3D, Material3DParams, LightParams3D}
use std.gpu.engine3d.texture3d.{TEX_FMT_RGBA8_UNORM}

var engine = Engine3D.create(800, 600)

# Render loop
engine.begin_frame()
engine.clear(0xFF111111)

# ... submit geometry ...

engine.end_frame()
engine.present()

val pixels = engine.read_pixels()

engine.shutdown()
```

`Engine3D.create(width, height)` auto-detects the best available backend. The framebuffer is `width * height` packed `u32` pixels in ARGB layout (`0xAARRGGBB`).

---

## Backend Selection

```simple
# Auto-detect (probes backends in priority order)
var engine = Engine3D.create(1280, 720)

# Explicit backend
var engine = Engine3D.create_with_backend(1280, 720, "cpu")
# Other names: "webgpu", "vulkan", "cuda", "rocm", "metal", "opengl"

# Query active backend
val name = engine.backend_name()   # -> "cpu"
```

Available backends: `cpu`, `software`, `cuda`, `vulkan`, `rocm`, `metal`, `opengl`, `intel`, `webgpu`, `qualcomm`, `baremetal`, `virtio_gpu`. Unknown names fall back to `cpu`.

---

## Geometry

### Triangle Primitive

The fundamental primitive is `submit_triangle`. All higher-level geometry is built from it.

```simple
use std.gpu.engine3d.types3d.{Vertex3D, Material3DParams}

val mat = Material3DParams(albedo: 0xFFFFFFFF, roughness: 0.5, metallic: 0.0, texture_id: -1, shader_type: 0)
val identity = [1.0f32, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0]

val v0 = Vertex3D(x: 0.0, y: 0.5, z: 0.0, nx: 0.0, ny: 0.0, nz: 1.0, u: 0.5, v: 0.0, color: 0xFFFF4400)
val v1 = Vertex3D(x: -0.5, y: -0.5, z: 0.0, nx: 0.0, ny: 0.0, nz: 1.0, u: 0.0, v: 1.0, color: 0xFF0044FF)
val v2 = Vertex3D(x: 0.5, y: -0.5, z: 0.0, nx: 0.0, ny: 0.0, nz: 1.0, u: 1.0, v: 1.0, color: 0xFF44FF00)
engine.submit_triangle(v0, v1, v2, mat, identity)
```

`Vertex3D` fields: `x, y, z` (position), `nx, ny, nz` (normal), `u, v` (UV), `color` (per-vertex ARGB tint).

### Built-in Shapes

```simple
# model is a column-major [f32; 16] transform matrix

engine.draw_cube(model, mat)
engine.draw_sphere(model, mat, 16)       # 16 segments
engine.draw_plane(model, mat)
engine.draw_cylinder(model, mat, 16)
engine.draw_cone(model, mat, 12)

# Line
engine.draw_line_3d(0.0, 0.0, 0.0, 1.0, 1.0, 1.0, 0xFFFFFFFF, 1.0)

# Wireframe
engine.draw_wireframe(vertices, indices, model, 0xFF00FF00)
```

### Indexed Mesh

```simple
engine.submit_indexed_mesh(vertices, indices, mat, model)
```

`vertices: [Vertex3D]`, `indices: [u32]` — the engine decomposes index triples into triangles.

### Instanced Mesh

```simple
# transforms: [[f32]] — one [f32;16] matrix per instance
engine.submit_mesh_instanced(vertices, indices, transforms, count, mat)
```

---

## Materials and Lighting

### Material Types

`Material3DParams` fields:

| Field | Type | Description |
|-------|------|-------------|
| `albedo` | `u32` | Base color in ARGB |
| `roughness` | `f32` | 0.0 (smooth) to 1.0 (rough) |
| `metallic` | `f32` | 0.0 (dielectric) to 1.0 (metal) |
| `texture_id` | `i32` | Bound texture id; -1 for none |
| `shader_type` | `i32` | 0 = unlit, 1 = Phong, 2 = PBR |

```simple
# Unlit
val mat_unlit = Material3DParams(albedo: 0xFFCC8844, roughness: 1.0, metallic: 0.0, texture_id: -1, shader_type: 0)

# Phong
val mat_phong = Material3DParams(albedo: 0xFFFFFFFF, roughness: 0.4, metallic: 0.0, texture_id: tex_handle.gpu_id, shader_type: 1)

# PBR
val mat_pbr = Material3DParams(albedo: 0xFFE0E0E0, roughness: 0.2, metallic: 0.9, texture_id: -1, shader_type: 2)
```

### Lights

```simple
use std.gpu.engine3d.types3d.{LightParams3D}

val lights = [
    LightParams3D(x: 5.0, y: 10.0, z: 5.0, color: 0xFFFFFFFF, intensity: 1.0, light_type: 0),  # point
    LightParams3D(x: -1.0, y: -1.0, z: -1.0, color: 0xFFCCCCFF, intensity: 0.8, light_type: 1)  # directional
]
engine.set_lights(lights)
engine.set_ambient(0xFF202040, 0.15)
```

`light_type`: 0 = point, 1 = directional, 2 = spot.

---

## Camera and View

Matrices are column-major `[f32; 16]`.

```simple
use std.gpu.engine3d.types3d.{mat4_perspective, mat4_look_at}

# Projection matrix: 60° FOV, 800/600 aspect, near=0.1, far=1000.0
val proj = mat4_perspective(1.047f32, 800.0 / 600.0, 0.1, 1000.0)

# View matrix: eye at (0,2,5), looking at origin, Y-up
val view = mat4_look_at(0.0, 2.0, 5.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0)

engine.set_camera(view, proj)

# Viewport sub-region (useful for split-screen)
engine.set_viewport(0, 0, 800, 600)
```

---

## Textures

### Loading Textures

```simple
use std.gpu.engine3d.resource_pool.{TextureHandle3D}

# 2D texture from pixel buffer
val tex: TextureHandle3D = engine.load_texture(256, 256, pixels)

# Volume texture
val vol: TextureHandle3D = engine.load_texture_3d(32, 32, 32, voxels)

# Cubemap — faces in +X, -X, +Y, -Y, +Z, -Z order
val cube: TextureHandle3D = engine.load_cubemap(512, faces)

# Depth texture (TEX_FMT_DEPTH32_FLOAT)
val depth: TextureHandle3D = engine.load_depth_texture(800, 600)

# Bind to a shader slot
engine.bind_texture(0, tex.gpu_id)

# Unload
engine.unload_texture(tex)
```

### Extended Texture Operations

```simple
use std.gpu.engine3d.texture3d.{TextureDescriptor3D, SamplerDescriptor3D, TextureView3D}
use std.gpu.engine3d.texture3d.{TEX_DIM_2D, TEX_FMT_RGBA8_UNORM, TEX_USAGE_TEXTURE_BINDING, TEX_USAGE_COPY_DST}

val desc = TextureDescriptor3D.create_2d(512, 512, TEX_FMT_RGBA8_UNORM)
val tex_id = engine.create_texture_ex(desc, raw_bytes)

engine.write_texture(tex_id, 0, 0, 0, 512, 512, 1, update_bytes)
engine.copy_texture_to_texture(src_id, dst_id, [0, 0, 0], [0, 0, 0], [256, 256, 1])
engine.generate_mipmaps(tex_id)

val sampler_desc = SamplerDescriptor3D(min_filter: 1, mag_filter: 1, mip_filter: 1, address_u: 0, address_v: 0, address_w: 0, lod_bias: 0.0, min_lod: 0.0, max_lod: 1000.0, compare_func: 0)
val sampler_id = engine.create_sampler(sampler_desc)

engine.destroy_texture_ex(tex_id)
engine.destroy_sampler(sampler_id)
```

---

## Resource Management

`ResourcePool3D` tracks all GPU resources and provides frame-age garbage collection.

```simple
use std.gpu.engine3d.resource_pool.{ResourcePool3D, TextureHandle3D, BufferHandle3D, ShaderHandle3D, PipelineHandle3D}

# GC resources unused for more than 3 frames
engine.gc_resources(3)

# Explicitly keep a resource alive this frame
engine.touch_resource(tex.id)

# Access the pool directly
val pool: ResourcePool3D = engine.resource_pool()
```

Each handle carries `id` (pool index) and `gpu_id` (backend resource ID). The `last_used_frame` field is updated by `touch_resource` and checked by `gc_resources`.

---

## Shaders and Pipelines

```simple
use std.gpu.engine3d.resource_pool.{ShaderHandle3D, PipelineHandle3D}

# Load a shader pair
val sh: ShaderHandle3D = engine.load_shader(vertex_src, fragment_src)

# Create a render pipeline from the shader
val pl: PipelineHandle3D = engine.load_pipeline(sh, true, 0, 1)
# args: shader, depth_test: bool, blend_mode: i32, cull_mode: i32

# Activate the pipeline
engine.bind_pipeline(pl.gpu_id)

# Unload
engine.unload_shader(sh)
```

`blend_mode`: 0 = opaque, 1 = alpha blend. `cull_mode`: 0 = none, 1 = back, 2 = front.

---

## Shadows

Shadow mapping requires a dedicated shadow pass before the main render pass.

```simple
# Shadow pass
val light_vp = mat4_multiply(light_proj, light_view)  # column-major [f32;16]
engine.begin_shadow_pass(light_vp, 1024)              # 1024x1024 shadow map

# Submit casters — only depth written
for each caster_mesh:
    engine.submit_shadow_caster(caster.vertices, caster.indices, caster.model)

engine.end_shadow_pass()

# Main pass — shadow map is automatically bound
engine.begin_frame()
engine.clear(0xFF000000)
# ... draw scene with shadowed materials ...
engine.end_frame()
engine.present()
```

---

## Post-Processing

Post effects are applied after geometry submission, before `present`:

```simple
# Fog — color, exponential density, near/far linear distances
engine.apply_fog(0xFF8899AA, 0.02, 10.0, 200.0)

# Bloom — threshold luminance, intensity scale
engine.apply_bloom(0.8, 1.5)

# Tonemap — Reinhard with exposure
engine.apply_tonemap(1.2)

# SSAO — ambient occlusion radius, bias, intensity
engine.apply_ssao(0.5, 0.025, 1.0)

# FXAA anti-aliasing (no parameters)
engine.apply_fxaa()

# Screen-space reflections — max raymarch steps, thickness
engine.apply_ssr(64, 0.1)
```

Effects are applied in call order. Typical order: fog → ssao → bloom → tonemap → fxaa.

---

## Render Passes

### Single Pass

```simple
engine.begin_render_pass(color_target_id, depth_target_id)
# ... geometry submission ...
engine.end_render_pass()
```

Pass targets are texture IDs created via `load_depth_texture` / `create_texture_ex` with `TEX_USAGE_RENDER_ATTACHMENT`.

### Multi-Pass with Compositor3D

```simple
use std.gpu.engine3d.compositor3d.{RenderPass3D, Compositor3D}

var comp = Compositor3D.create(800, 600)

var shadow_pass = RenderPass3D.create("shadow", 800, 600)
shadow_pass.set_z_order(0)

var main_pass = RenderPass3D.create("main", 800, 600)
main_pass.set_z_order(1)

var ui_pass = RenderPass3D.create("ui", 800, 600)
ui_pass.set_z_order(2)

comp.add_pass(shadow_pass)
comp.add_pass(main_pass)
comp.add_pass(ui_pass)
comp.sort_passes()

# Render into each pass independently, then composite
val final_frame = comp.composite()
```

`composite()` alpha-blends passes in z_order using per-pixel alpha from `pixels[px]`.

---

## Compute

GPU compute kernels run alongside the 3D pipeline.

```simple
# Create a kernel from compute shader source (WGSL or GLSL)
val kernel_id = engine.create_compute_kernel(compute_src)

# Dispatch — workgroup counts (not thread counts)
engine.dispatch_compute(kernel_id, 64, 1, 1)

# Read back results via a storage buffer
val buf = engine.load_buffer(4096)
engine.update_buffer(buf.gpu_id, input_bytes)
engine.dispatch_compute(kernel_id, 16, 1, 1)
val result = engine.read_buffer(buf.gpu_id)
engine.unload_buffer(buf)
```

The compute path shares the same resource pool and bind group system as the render pipeline.

---

## See Also

- [WebGPU Integration Guide](../api/webgpu_guide.md) — WebGPU backend and browser context
- [GPU Compute API](../api/gpu_api.md) — underlying GPU compute and 3D engine API reference
- [std.gpu.engine3d source](../../../src/lib/gc_async_mut/gpu/engine3d/) — source files
