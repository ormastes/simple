# WebGPU Integration Guide

Covers the WebGPU surface in Simple: the 3D engine WebGPU backend, browser WebGPU context, Chrome-compatible type system, HTTP server asset middleware, and canvas integration.

---

## Overview

Simple exposes WebGPU in three places:

1. **3D Engine WebGPU Backend** — `std.gpu.engine3d` backend that implements `RenderBackend3D` + `Engine3DExtended` using WebGPU primitives. Works both in-browser (via JS bridge) and natively.
2. **HTTP Server Asset Middleware** — `std.http_server.webgpu_assets` serves WGSL shaders, SPIR-V binaries, and compressed textures with correct MIME types, plus cross-origin isolation headers required for `SharedArrayBuffer`.
3. **Browser Canvas Integration** — browser canvas elements support `CANVAS_CONTEXT_WEBGPU`, and 3D transforms route through `composite_to_gpu.spl`.

All WebGPU types in the engine mirror the Chrome WebGPU API (`GPUTexture`, `GPUSampler`, `GPURenderPipeline`, etc.) for portability.

---

## 3D Engine WebGPU Backend

**Source:** `src/lib/gc_async_mut/gpu/engine3d/backend_webgpu.spl`

The WebGPU backend implements both `RenderBackend3D` (Core 32 + Adv 42 methods) and `Engine3DExtended` (20 Chrome WebGPU extension methods). It is selected via `Engine3D.create_with_backend`:

```simple
use std.gpu.engine3d.engine.{Engine3D}

# Auto-select (currently selects CPU; WebGPU probed in future)
var engine = Engine3D.create(1280, 720)

# Explicit WebGPU backend
var engine = Engine3D.create_with_backend(1280, 720, "webgpu")
```

The backend provides a per-vertex Phong lighting rasterizer and a scanline triangle rasterizer as its software fallback path. Hardware WebGPU dispatch calls are routed through `ffi_dispatch3d.spl`.

### Engine3DExtended — Chrome WebGPU Features

The `Engine3DExtended` trait adds 20 methods that WebGPU-capable backends implement:

```simple
use std.gpu.engine3d.backend.{Engine3DExtended}

# MSAA
engine.enable_msaa(4)

# Clip planes
engine.set_clip_planes([[0.0, 1.0, 0.0, -1.0]])

# Subgroup operations (compute shaders)
engine.enable_subgroup_ops(true)

# Dual-source blending
engine.set_dual_source_blend(true)

# HDR render target
engine.enable_hdr_render_target(true)

# Ray tracing (Vulkan VK_KHR_ray_tracing / OptiX)
val accel = engine.build_acceleration_structure(vertices, indices)
val hits = engine.trace_rays(accel, ray_count, origins, directions)

# Variable rate shading
engine.set_variable_rate_shading(1)

# Mesh shaders (experimental)
engine.set_mesh_shader_enabled(true)

# Bind groups (Chrome WebGPU parity)
val layout_id = engine.create_bind_group_layout(entries)
val bg_id = engine.create_bind_group(layout_id, entries)
engine.set_bind_group(0, bg_id)
engine.destroy_bind_group(bg_id)
```

---

## Browser WebGPU Context

**Source:** `examples/browser/feature/gpu/webgpu_context.spl`

The browser WebGPU context follows MDSOC+ capsule architecture. It manages the full adapter/device lifecycle for in-browser rendering.

Key flow:

```simple
# Request adapter
val adapter = webgpu_context.request_adapter()

# Request device with limits
val device_desc = GPUDeviceDescriptor(
    required_features: ["texture-compression-bc"],
    required_limits: GPUDeviceLimits.default()
)
val device = adapter.request_device(device_desc)

# Configure canvas
val config = GPUCanvasConfiguration(
    device: device,
    format: "bgra8unorm",
    usage: TEX_USAGE_RENDER_ATTACHMENT,
    alpha_mode: "opaque"
)
canvas.configure(config)
```

### Chrome WebGPU Types

These types mirror the Chrome WebGPU API and live in the engine's type system:

| Type | Fields | Description |
|------|--------|-------------|
| `GPUAdapterInfo` | `vendor, architecture, device, description: text` | Adapter identity |
| `GPUDeviceLimits` | `max_texture_dimension_2d, max_texture_dimension_3d, max_bind_groups, max_uniform_buffer_binding_size: i32` | Device capability limits |
| `GPUDeviceDescriptor` | `required_features: [text]`; `required_limits: GPUDeviceLimits` | Device creation parameters |
| `GPUCanvasConfiguration` | `format: text`; `usage: i32`; `alpha_mode: text` | Canvas swap-chain config |

**Feature string constants** (pass in `required_features`):
- `"texture-compression-bc"` — BC1/BC3/BC7 compressed textures
- `"texture-compression-etc2"` — ETC2 (mobile)
- `"texture-compression-astc"` — ASTC
- `"depth-clip-control"` — depth clipping
- `"timestamp-query"` — GPU timing
- `"indirect-first-instance"` — instanced indirect draw

---

## Texture System

### TextureDescriptor3D

```simple
use std.gpu.engine3d.texture3d.{TextureDescriptor3D, TEX_DIM_2D, TEX_DIM_3D, TEX_DIM_CUBE, TEX_FMT_RGBA8_UNORM, TEX_FMT_DEPTH32_FLOAT, TEX_USAGE_TEXTURE_BINDING, TEX_USAGE_COPY_DST}

# 2D texture
val desc2d = TextureDescriptor3D.create_2d(512, 512, TEX_FMT_RGBA8_UNORM)

# Volume texture
val desc3d = TextureDescriptor3D.create_3d(64, 64, 64, TEX_FMT_RGBA16_FLOAT)

# Cubemap (depth_or_layers = 6)
val desc_cube = TextureDescriptor3D(
    dimension: TEX_DIM_CUBE,
    format: TEX_FMT_RGBA8_UNORM,
    width: 512, height: 512,
    depth_or_layers: 6,
    mip_level_count: 1,
    sample_count: 1,
    usage: TEX_USAGE_TEXTURE_BINDING | TEX_USAGE_COPY_DST
)
```

### Texture Dimensions

| Constant | Value | Description |
|----------|-------|-------------|
| `TEX_DIM_2D` | 0 | Standard 2D texture |
| `TEX_DIM_3D` | 1 | Volume texture |
| `TEX_DIM_CUBE` | 2 | Cubemap (6 faces) |
| `TEX_DIM_2D_ARRAY` | 3 | Array of 2D textures |
| `TEX_DIM_CUBE_ARRAY` | 4 | Array of cubemaps |

### Texture Formats

| Constant | Description |
|----------|-------------|
| `TEX_FMT_RGBA8_UNORM` | Standard RGBA 8-bit |
| `TEX_FMT_RGBA8_SRGB` | sRGB RGBA 8-bit |
| `TEX_FMT_BGRA8_UNORM` | BGRA (swap-chain default) |
| `TEX_FMT_RGBA16_FLOAT` | HDR half-float |
| `TEX_FMT_RGBA32_FLOAT` | HDR full-float |
| `TEX_FMT_DEPTH32_FLOAT` | Depth-only |
| `TEX_FMT_DEPTH24_PLUS` | 24-bit depth |
| `TEX_FMT_DEPTH24_PLUS_STENCIL8` | Depth + stencil |
| `TEX_FMT_BC1_UNORM` | BC1/DXT1 compressed |
| `TEX_FMT_BC3_UNORM` | BC3/DXT5 compressed |
| `TEX_FMT_BC7_UNORM` | BC7 high-quality compressed |
| `TEX_FMT_ETC2_RGB8` | ETC2 (mobile) |
| `TEX_FMT_ASTC_4X4` | ASTC 4x4 |

### Usage Flags

| Constant | Value | Description |
|----------|-------|-------------|
| `TEX_USAGE_TEXTURE_BINDING` | 1 | Bind as shader texture |
| `TEX_USAGE_STORAGE_BINDING` | 2 | Bind as storage texture |
| `TEX_USAGE_RENDER_ATTACHMENT` | 4 | Use as render target |
| `TEX_USAGE_COPY_SRC` | 8 | Copy source |
| `TEX_USAGE_COPY_DST` | 16 | Copy destination |

### SamplerDescriptor3D

```simple
use std.gpu.engine3d.texture3d.{SamplerDescriptor3D}

val sampler = SamplerDescriptor3D(
    min_filter: 1,       # LINEAR
    mag_filter: 1,       # LINEAR
    mip_filter: 1,       # LINEAR
    address_u: 0,        # CLAMP_TO_EDGE
    address_v: 0,
    address_w: 0,
    lod_bias: 0.0,
    min_lod: 0.0,
    max_lod: 1000.0,
    compare_func: 0      # none
)
val sampler_id = engine.create_sampler(sampler)
```

---

## Shader and Pipeline

### ShaderModule3D

```simple
use std.gpu.engine3d.shader3d.{ShaderModule3D, RenderPipelineDescriptor3D, ComputePipelineDescriptor3D}

val shader = ShaderModule3D(
    vertex_src: "... WGSL or GLSL vertex source ...",
    fragment_src: "... fragment source ...",
    compute_src: ""
)
val shader_handle = engine.load_shader(shader.vertex_src, shader.fragment_src)
```

### Vertex Layout

```simple
use std.gpu.engine3d.shader3d.{VertexAttribute3D, VertexBufferLayout3D}
use std.gpu.engine3d.shader3d.{VERTEX_FMT_FLOAT32X3, VERTEX_FMT_FLOAT32X2}

val attrs = [
    VertexAttribute3D(location: 0, format: VERTEX_FMT_FLOAT32X3, offset: 0),   # position
    VertexAttribute3D(location: 1, format: VERTEX_FMT_FLOAT32X3, offset: 12),  # normal
    VertexAttribute3D(location: 2, format: VERTEX_FMT_FLOAT32X2, offset: 24)   # uv
]
val layout = VertexBufferLayout3D(stride: 32, attributes: attrs)
```

### Render Pipeline

```simple
val desc = RenderPipelineDescriptor3D(
    shader_id: shader_handle.gpu_id,
    vertex_layout_id: 0,
    depth_test: 1,
    cull_mode: 1,     # back-face cull
    blend_mode: 0,    # opaque
    topology: 0       # TRIANGLE_LIST
)
val pipeline = engine.load_pipeline(shader_handle, true, 0, 1)
```

### Compute Pipeline

```simple
val compute = ComputePipelineDescriptor3D(
    shader_id: shader_handle.gpu_id,
    entry_point: "main"
)
val kernel_id = engine.create_compute_kernel(compute_src)
engine.dispatch_compute(kernel_id, 64, 1, 1)
```

---

## Bind Groups

Bind groups associate shader resource slots with GPU buffers, textures, and samplers.

```simple
use std.gpu.engine3d.bind_group3d.{BindGroupLayoutEntry3D, BindGroupEntry3D, BindGroup3D}
use std.gpu.engine3d.bind_group3d.{VISIBILITY_VERTEX, VISIBILITY_FRAGMENT, VISIBILITY_COMPUTE}
use std.gpu.engine3d.bind_group3d.{standard_mvp_layout, standard_material_layout, standard_lighting_layout}

# Create a layout
val entries = [
    BindGroupLayoutEntry3D.uniform(0, VISIBILITY_VERTEX, 64),
    BindGroupLayoutEntry3D.texture(1, VISIBILITY_FRAGMENT),
    BindGroupLayoutEntry3D.sampler(2, VISIBILITY_FRAGMENT)
]
val layout_id = engine.create_bind_group_layout(entries)

# Bind resources
val bg_entries = [
    BindGroupEntry3D.buffer(0, mvp_buf_id, 0, 64),
    BindGroupEntry3D.texture(1, tex_handle.gpu_id),
    BindGroupEntry3D.sampler(2, sampler_id)
]
val bg_id = engine.create_bind_group(layout_id, bg_entries)
engine.set_bind_group(0, bg_id)

# Clean up
engine.destroy_bind_group(bg_id)
```

### Standard Layout Presets

```simple
use std.gpu.engine3d.bind_group3d.{standard_mvp_layout, standard_material_layout, standard_lighting_layout}

# MVP matrix layout: binding 0, vertex-visible, 64 bytes (mat4)
val mvp_layout = standard_mvp_layout()

# Material layout: binding 0 (32 bytes, fragment), binding 1 (texture), binding 2 (sampler)
val mat_layout = standard_material_layout()

# Lighting layout: binding 0, fragment-visible, 512 bytes (light array)
val light_layout = standard_lighting_layout()
```

---

## HTTP Server WebGPU Support

**Source:** `src/lib/nogc_async_mut/http_server/webgpu_assets.spl`

**Import:** `use std.http_server.webgpu_assets.{webgpu_mime_type, is_webgpu_asset, cross_origin_isolation_headers, is_shader_file, is_compressed_texture_file}`

### MIME Types

| Extension | MIME Type |
|-----------|-----------|
| `.wgsl` | `text/wgsl` |
| `.spv` | `application/x-spv` |
| `.ktx2` | `image/ktx2` |
| `.basis` | `application/octet-stream` |
| `.dds` | `image/vnd-ms.dds` |
| `.glsl`, `.vert`, `.frag` | `text/plain` |

```simple
use std.http_server.webgpu_assets.{webgpu_mime_type, is_webgpu_asset}

val mime = webgpu_mime_type(".wgsl")   # "text/wgsl"
val ok   = is_webgpu_asset(".ktx2")   # true
```

### Cross-Origin Isolation Headers

Required for `SharedArrayBuffer` (used by WebGPU compute and WASM threads):

```simple
use std.http_server.webgpu_assets.{cross_origin_isolation_headers}

# Returns: [["Cross-Origin-Opener-Policy", "same-origin"],
#           ["Cross-Origin-Embedder-Policy", "require-corp"],
#           ["Cross-Origin-Resource-Policy", "cross-origin"]]
val headers = cross_origin_isolation_headers()
```

Apply these headers to any response that needs `SharedArrayBuffer` access.

### Asset Type Checks

```simple
use std.http_server.webgpu_assets.{is_shader_file, is_compressed_texture_file}

is_shader_file(".wgsl")   # true — WGSL, GLSL, .vert, .frag, .spv
is_compressed_texture_file(".ktx2")  # true — KTX2, Basis, DDS
```

---

## Canvas Integration

Browser canvas elements support WebGPU contexts via `CANVAS_CONTEXT_WEBGPU`. The browser engine detects 3D CSS transforms and routes compositing through `composite_to_gpu.spl`.

```simple
# Request a WebGPU context on a canvas element
val ctx = canvas_element.get_context(CANVAS_CONTEXT_WEBGPU)

# Attach the swap-chain
val config = GPUCanvasConfiguration(
    format: "bgra8unorm",
    usage: TEX_USAGE_RENDER_ATTACHMENT,
    alpha_mode: "opaque"
)
ctx.configure(config)

# Get current frame texture
val frame_tex = ctx.get_current_texture()
```

3D transform detection in `composite_to_gpu.spl` checks for `transform3d` CSS properties and promotes those layers to GPU compositing automatically.

---

## See Also

- [3D Engine Library Guide](../library/engine3d.md) — higher-level usage
- [GPU Compute API](gpu_api.md) — underlying GPU compute layer
- [std.gpu.engine3d module](../../../src/lib/gc_async_mut/gpu/engine3d/) — source
