# SStack State: 3d-engine-gpu-webgpu

## User Request
> impl 3d engine gpu + webgpu, minimize duplication with agent teams. see doc/03_plan/remaining_roadmap.md

## Task Type
feature

## Refined Goal
> Upgrade the 3D engine from CPU-only software rendering to GPU-accelerated rendering with a unified backend trait supporting Vulkan, WebGPU, and software fallback. Follow established codebase patterns (game2d trait-based backends, Skia Vulkan command-buffer recording, physics GpuSolver upload→dispatch→download, MDSOC+ outer/business separation). Implement in parallel agent workstreams with disjoint file scopes.

## Current State Assessment
- **ForwardRenderer3D** (555 lines): Full CPU software rasterizer with MVP pipeline, depth testing, Phong shading — functional, serves as software fallback
- **gpu/context.spl**: Unified `Context` type exists but only CUDA/PyTorch backed; Vulkan commented out; no WebGPU
- **gpu_bridge.spl + gpu_pipeline.spl**: Wire to Context but all shader handles are 0 placeholders
- **ShaderSource/ShaderGraph**: GLSL text storage + visual shader DAG, but no compilation pipeline (no SPIR-V, no WGSL)
- **GpuParticleSystem**: Has ParticleBackend enum but compute dispatch is stub-level
- **Material3D**: PBR/Phong/Unlit type enum exists; albedo_texture always `TextureId.invalid()`
- **Skia Vulkan backend**: Command-buffer recording pattern with `VkCommand` enum — proven pattern to follow
- **game2d GameBackend trait**: Trait-based with composition, SdlBackend + HeadlessBackend — proven pattern
- **Physics GpuSolver**: Upload→dispatch per color-batch→download with `PhysicsBackend` enum — render should mirror

## Acceptance Criteria
- [ ] AC-1: `RenderBackend3D` trait defined with Vulkan, WebGPU, and Software implementations (follows GameBackend trait pattern)
- [ ] AC-2: `RenderCapability3D` struct + backend detection (follows SkCapability pattern)
- [ ] AC-3: GPU mesh pipeline: vertex buffer upload, GPU-side MVP transforms, indexed draw calls through backend trait
- [ ] AC-4: GPU-accelerated lighting (point/directional/spot) via compute or fragment shader path
- [ ] AC-5: Shader cross-compilation: GLSL→SPIR-V (Vulkan) and GLSL→WGSL (WebGPU) with `ShaderProgram` wired to real handles
- [ ] AC-6: WebGPU shim: `rt_wgpu_*` extern declarations + Rust runtime stubs for browser target
- [ ] AC-7: 3D texture system: GPU texture upload, Material3D→pipeline state binding, texture atlas/cache
- [ ] AC-8: MDSOC+ audit: engine3d outer layer owns policy/orchestration, ECS business layer owns data, no cross-imports
- [ ] AC-9: Existing ForwardRenderer3D preserved as `SoftwareRenderBackend3D` fallback (no regression)
- [ ] AC-10: All new code uses MDSOC+ patterns — no inheritance, trait+composition only, tagged enum dispatch for variants

## Parallel Agent Workstreams (Phase 5)
| Stream | Files (disjoint scope) | ACs |
|--------|----------------------|-----|
| A: Backend Trait + Capability | `engine/render/backend3d.spl`, `engine/render/capability3d.spl`, `engine/render/software_backend3d.spl` | AC-1, AC-2, AC-9 |
| B: Vulkan Backend | `engine/render/vulkan_backend3d.spl`, `engine/render/vulkan_commands.spl` | AC-1 (Vulkan impl) |
| C: WebGPU Backend + Runtime | `engine/render/webgpu_backend3d.spl`, `engine/render/webgpu_commands.spl`, runtime `rt_wgpu_*` stubs | AC-1 (WebGPU impl), AC-6 |
| D: GPU Mesh + Lighting | `engine/render/gpu_mesh3d.spl`, `engine/render/gpu_lighting3d.spl`, updates to `gpu_bridge.spl` | AC-3, AC-4 |
| E: Shader Pipeline | `engine/render/shader_compile.spl`, `engine/render/wgsl_emitter.spl`, updates to `shader.spl` | AC-5 |
| F: Texture + Material | `engine/render/texture3d.spl`, `engine/render/texture_atlas3d.spl`, updates to `material3d.spl` | AC-7 |

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-10
- [x] 2-research (Analyst) — 2026-05-10
- [ ] 3-arch (Architect)
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
**Task type:** feature
**Refined goal:** GPU-accelerate the 3D engine with unified RenderBackend3D trait (Vulkan + WebGPU + Software fallback), following established codebase patterns.

**Key decisions:**
1. Follow `GameBackend` trait pattern (not enum dispatch) for `RenderBackend3D`
2. Follow `SkCapability` pattern for `RenderCapability3D`
3. Mirror physics `GpuSolver` upload→dispatch→download for mesh pipeline
4. Follow Skia `VkCommand` command-buffer recording pattern for Vulkan/WebGPU backends
5. Keep `ForwardRenderer3D` as software fallback — wrap it, don't replace it
6. CUDA FFI `extern fn rt_*` flat pattern for WebGPU runtime bindings
7. 6 parallel agent workstreams with disjoint file scopes for Phase 5

**Risk:** Shader compilation (AC-5) depends on runtime externs (`rt_vulkan_compile_glsl`) that don't exist yet — may need Rust runtime work in `src/compiler_rust/` or `src/runtime/`.

### 2-research

**Runtime externs inventory:**

*WebGPU (fully wired, stub+real modes):*
- `rt_webgpu_is_available() -> bool`
- `rt_webgpu_init() -> bool`
- `rt_webgpu_shutdown() -> bool`
- `rt_webgpu_create_surface(width: i32, height: i32) -> i64`
- `rt_webgpu_destroy_surface(handle: i64) -> bool`
- `rt_webgpu_upload_pixels(handle: i64, pixels: [u32], w: i32, h: i32) -> bool`
- `rt_webgpu_present(handle: i64) -> bool`
- `rt_webgpu_compute_draw(handle: i64, op_kind: i32, ...) -> bool`
- Backed by `src/runtime/hosted/webgpu.rs`; stub=default, real=`--features webgpu-real`

*Vulkan (compute path only, declared in gc_async engine2d):*
- `rt_vulkan_init/shutdown/is_available/device_count/select_device -> bool/i64`
- `rt_vulkan_alloc_buffer / free_buffer / copy_to_buffer / copy_from_buffer`
- `rt_vulkan_compile_glsl(glsl_source: text) -> i64` — **extern declared, runtime impl unknown**
- `rt_vulkan_destroy_shader / create_compute_pipeline / destroy_pipeline`
- `rt_vulkan_create_descriptor_set / bind_buffer / destroy_descriptor_set`
- `rt_vulkan_begin_compute / bind_pipeline / bind_descriptors / push_constants / dispatch / end_compute / submit_and_wait / wait_idle`
- Source: `src/lib/gc_async_mut/gpu/engine2d/ffi_vulkan.spl` + `backend_vulkan.spl` — **no graphics pipeline externs** (no draw_indexed, no render pass, no swapchain)

*Image loading (available):*
- `rt_image_load(path) -> i64`, `rt_image_free`, `rt_image_width`, `rt_image_height`, `rt_image_channels`, `rt_image_get_pixel`
- Source: `src/runtime/runtime_image.c` using vendored `stb_image.h`

*CUDA (available):*
- Full set in `src/lib/nogc_sync_mut/cuda/ffi.spl` — init, device, ctx, mem alloc/copy, module load, kernel launch, sync

*GPU memory (nogc context, PyTorch/CUDA backed):*
- `rt_dyn_torch_tensor_from_bits_1d`, `rt_torch_to_cuda/cpu/free/clone`
- `src/lib/nogc_sync_mut/gpu/memory.spl` GpuArray<T> with upload/download

**Critical gaps found:**
- `rt_vulkan_compile_glsl` is declared as extern but **no runtime C/Rust implementation found** in `src/runtime/` — it's a declaration without a backing symbol
- No `rt_vulkan_*` **graphics** externs: no render pass, swapchain, framebuffer, vertex buffer draw — only compute externs exist
- `signatures.rs` has **no GPU externs registered** — confirms GPU externs bypass the interpreter and only work in compiled/native mode
- No `rt_wgpu_*` 3D-specific externs (existing WebGPU is pixel-upload only, not a 3D pipeline)
- `GpuTextureCache.upload_texture_to_gpu()` calls `ctx.create_texture()` but `Context` has no such method — the method call is a placeholder stub

**Existing gc_async_mut engine3d (major reuse opportunity):**
- `src/lib/gc_async_mut/gpu/engine3d/` has a **complete parallel 3D backend system**:
  - `backend_core.spl`: `trait RenderBackend3DCore` with `fn name`, `fn read_pixels -> [u32]`, `fn read_depth -> [f32]`, `fn width/height`
  - `backend_adv.spl`: `trait RenderBackend3DAdv` extending core with emulation layer
  - Implementations: `backend_cpu.spl` (CpuBackend3D), `backend_cuda.spl` (CudaBackend3D), `backend_vulkan.spl`, `backend_webgpu.spl`, `backend_software.spl`, `backend_baremetal.spl`, `backend_metal.spl`, `backend_opengl.spl`, `backend_rocm.spl`, `backend_intel.spl`, `backend_qualcomm.spl`, `backend_virtio_gpu.spl`
  - `types3d.spl`: Vertex3D, Material3DParams, LightParams3D, RenderStats3D, full mat4 math
  - `shader3d.spl`, `texture3d.spl`, `bind_group3d.spl`, `resource_pool.spl`, `ffi_vulkan3d.spl`, `ffi_cuda3d.spl`
- **These are in gc_async_mut (different layer than the target nogc_sync_mut engine)**

**Engine3D / ForwardRenderer3D wiring:**
- `Engine3D` struct owns `renderer: ForwardRenderer3D` directly (not trait-boxed)
- `ForwardRenderer3D.create(width, height)` — pure CPU rasterizer, 555 lines
- `GameLoop3D` drives `on_render: fn(Engine3D, FrameTime)` callback
- To add backend trait: Engine3D needs a `render_backend: RenderBackend3D` field alongside/replacing `renderer: ForwardRenderer3D`

**Shader pipeline state:**
- `shader.spl`: `ShaderSource` (vertex_code + fragment_code text), `ShaderProgram` (handle pair, `is_compiled: false`)
- `create_shader_program()` explicitly comments: "rt_vulkan_compile_glsl runtime support (not yet implemented)"
- Builtin 2D + 3D GLSL shaders exist as text in `shader.spl`
- `shader_graph.spl`: full DAG model (ShaderNode, ShaderPort, ShaderConnection, ShaderGraph) — visual editor data only

**gpu_bridge.spl / gpu_pipeline.spl wiring:**
- `GpuRenderState`: render_pass, pipeline, swapchain, framebuffer, color_texture — all created via `ctx.*` calls
- `ctx.create_render_pass/swapchain/texture/framebuffer/create_graphics_pipeline` are called but `Context` class **does not define these methods** — they are aspirational stubs calling non-existent Context API
- `begin_gpu_frame / submit_gpu_batch / end_gpu_frame` exist but are no-ops when `is_initialized == false` (always false until Context grows the methods)

**Material3D:**
- `albedo_texture: TextureId` always `.invalid()` in constructors
- `has_texture()` method exists but is never true in practice
- No GPU binding path exists

**GpuTextureCache:**
- `GpuTextureCache.entries: Dict<i64, GpuTexture>`, `upload_count`
- `upload_texture_to_gpu(ctx, texture)` stub — returns placeholder GpuTexture
- `get_or_upload(cache, ctx, tex_id, store)` — logic correct, upload impl is stub

**Physics GpuSolver pattern (confirmed upload→dispatch→download):**
- `GpuSolver.solve()`: `upload_bodies → upload_constraints → dispatch_velocity_solve (per color) → dispatch_position_solve (per color) → download_results`
- All dispatch methods are TODO stubs pointing to `rt_cuda_launch_kernel`
- `PhysicsBackend` enum: CpuScalar/CpuSimd/Cuda/VulkanCompute/Auto with `select_backend()` fn

**GameBackend trait (game2d):**
- `game_backend.spl` file not found as a standalone trait file — may be inline in engine2d. The math `backend.spl` is a different file (MathBackend enum for m{} expressions)
- gc_async engine3d uses `trait RenderBackend3DCore` + `trait RenderBackend3DAdv` — this IS the proven trait pattern to follow

## Research Summary

### Existing Code
- `src/lib/gc_async_mut/gpu/engine3d/backend_core.spl:26-80` — `trait RenderBackend3DCore`: name, draw_triangle_3d, clear, present, read_pixels, read_depth, width, height — **the trait to port/bridge**
- `src/lib/gc_async_mut/gpu/engine3d/backend_adv.spl:25+` — `trait RenderBackend3DAdv`: emulation layer on top of core
- `src/lib/gc_async_mut/gpu/engine3d/backend_cpu.spl` — CpuBackend3D (full software rasterizer, similar to ForwardRenderer3D — check for dedup)
- `src/lib/gc_async_mut/gpu/engine3d/backend_vulkan.spl` — VulkanBackend3D stub
- `src/lib/gc_async_mut/gpu/engine3d/backend_webgpu.spl` — WebGpuBackend3D stub
- `src/lib/gc_async_mut/gpu/engine3d/types3d.spl:20-215` — Vertex3D, mat4 math, LightParams3D, Material3DParams, RenderStats3D — reuse directly
- `src/lib/gc_async_mut/gpu/engine2d/ffi_vulkan.spl:22-45` — full `rt_vulkan_*` extern set (compute path)
- `src/lib/gc_async_mut/gpu/engine2d/backend_webgpu.spl` — `rt_webgpu_*` extern declarations + WebGpuBackend class
- `src/runtime/hosted/webgpu.rs` — WebGPU runtime: stub + real (`--features webgpu-real`)
- `src/runtime/runtime_image.c` — `rt_image_load/free/width/height/channels/get_pixel` via stb_image
- `src/lib/nogc_sync_mut/engine/render/renderer3d.spl` — ForwardRenderer3D (555 lines, pure CPU)
- `src/lib/nogc_sync_mut/engine/render/gpu_bridge.spl` — GpuRenderState + frame ops (aspirational stubs)
- `src/lib/nogc_sync_mut/engine/render/gpu_texture_cache.spl` — GpuTextureCache pattern (stub upload)
- `src/lib/nogc_sync_mut/engine/render/shader.spl` — ShaderSource, ShaderProgram, builtin GLSL texts
- `src/lib/nogc_sync_mut/engine/render/material3d.spl` — Material3D with TextureId (always invalid)
- `src/lib/nogc_sync_mut/engine/core/engine3d.spl` — Engine3D owns `renderer: ForwardRenderer3D` (not trait-boxed)
- `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` — GpuSolver upload→dispatch→download pattern
- `src/lib/nogc_sync_mut/cuda/ffi.spl:11-57` — full `rt_cuda_*` extern set

### Reusable Modules
- `gc_async_mut/gpu/engine3d/types3d.spl` — Vertex3D, mat4, lights, materials (reuse or reference)
- `gc_async_mut/gpu/engine3d/backend_core.spl` + `backend_adv.spl` — trait definitions to port to nogc layer
- `gc_async_mut/gpu/engine2d/ffi_vulkan.spl` — `rt_vulkan_*` compute externs (bridge to graphics needs new externs)
- `gc_async_mut/gpu/engine2d/backend_webgpu.spl` — `rt_webgpu_*` extern declarations to extend for 3D
- `nogc_sync_mut/engine/render/gpu_texture_cache.spl` — `GpuTextureCache` (extend `upload_texture_to_gpu`)
- `nogc_sync_mut/engine/render/gpu_bridge.spl` — `GpuRenderState` frame lifecycle (extend with real Context calls)
- `nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` — dispatch pattern for mesh/lighting compute

### Domain Notes
- WebGPU runtime (`webgpu.rs`) is **pixel-upload only** — no vertex buffers, no render pipeline, no shader compilation. For 3D GPU draw calls, it must be extended with `rt_webgpu_create_vertex_buffer`, `rt_webgpu_create_pipeline`, `rt_webgpu_draw_indexed` etc., or the 3D path uses the pixel-upload surface as a framebuffer target (software rasterize → upload pixels → present).
- `rt_vulkan_compile_glsl` is declared as an extern in the spl files but **has no C/Rust backing symbol in src/runtime/**. Implementing AC-5 requires either: (a) adding a Rust `shaderc` binding in `src/runtime/hosted/` or a C shaderc wrapper, or (b) using pre-compiled SPIR-V embedded as bytes.
- The `nogc_sync_mut` layer has no `trait` dispatch mechanism for GPU backends in the 3D engine — the gc_async layer does. Stream A must introduce the trait to the nogc layer.
- `Context.create_texture/create_render_pass/create_swapchain` do not exist — `gpu_bridge.spl` calls them speculatively. These must be added to `Context` as part of this feature (or gpu_bridge must be rewired to use `rt_vulkan_*` / `rt_webgpu_*` externs directly).
- ForwardRenderer3D and gc_async CpuBackend3D likely duplicate rasterization logic — check before implementing SoftwareRenderBackend3D.

### Open Questions
- NONE

## Requirements
- REQ-1 (from AC-1): Define `trait RenderBackend3D` in nogc_sync_mut engine layer, following `RenderBackend3DCore` pattern from gc_async — area: `src/lib/nogc_sync_mut/engine/render/backend3d.spl` (new)
- REQ-2 (from AC-2): Define `RenderCapability3D` struct + `detect_render_backend()` fn following `SkCapability` / `PhysicsBackend.select_backend()` pattern — area: `src/lib/nogc_sync_mut/engine/render/capability3d.spl` (new)
- REQ-3 (from AC-3): GPU mesh pipeline: vertex buffer upload + indexed draw via backend trait; wire `gpu_bridge.spl` to real `rt_vulkan_*` graphics externs (currently aspirational stubs) — area: `src/lib/nogc_sync_mut/engine/render/gpu_mesh3d.spl` (new) + `gpu_bridge.spl` (extend)
- REQ-4 (from AC-4): Lighting compute via fragment shader or compute dispatch; reuse `rt_vulkan_*` compute pipeline externs from `ffi_vulkan.spl` — area: `src/lib/nogc_sync_mut/engine/render/gpu_lighting3d.spl` (new)
- REQ-5 (from AC-5): Shader cross-compilation: `rt_vulkan_compile_glsl` needs runtime implementation (currently extern-only, no backing symbol); WGSL emitter for WebGPU path — area: `src/runtime/hosted/` (new vulkan shader compiler) + `src/lib/nogc_sync_mut/engine/render/shader_compile.spl` (new)
- REQ-6 (from AC-6): WebGPU shim: extend `rt_webgpu_*` externs for 3D pipeline (vertex buffers, draw calls) or adopt pixel-upload framebuffer strategy — area: `src/runtime/hosted/webgpu.rs` (extend) + `src/lib/nogc_sync_mut/engine/render/webgpu_backend3d.spl` (new)
- REQ-7 (from AC-7): 3D texture system: wire `rt_image_load` → `GpuTextureCache.upload_texture_to_gpu()` (currently stub) → `Material3D.albedo_texture` → pipeline binding — area: `src/lib/nogc_sync_mut/engine/render/texture3d.spl` (new) + `gpu_texture_cache.spl` (extend) + `material3d.spl` (extend)
- REQ-8 (from AC-8): MDSOC+ audit — Engine3D outer layer owns policy; no cross-imports between render/physics/audio subsystems — area: `src/lib/nogc_sync_mut/engine/`
- REQ-9 (from AC-9): Wrap ForwardRenderer3D as `SoftwareRenderBackend3D` implementing `RenderBackend3D` trait; Engine3D gains `render_backend` field — area: `src/lib/nogc_sync_mut/engine/render/software_backend3d.spl` (new) + `engine3d.spl` (modify)
- REQ-10 (from AC-10): All new files use trait+composition, no inheritance, tagged enum for backend dispatch — pattern: `GpuSolver` + `RenderBackend3DCore` from gc_async

## Phase
research-done

## Log
- 1-dev (2026-05-10): Created state file with 10 acceptance criteria, 6 parallel workstreams
- 2-research (2026-05-10): Found 32 existing files across gc_async engine3d + nogc engine render; identified 8 rt_webgpu_* externs (wired), 18 rt_vulkan_* compute externs (declared, no graphics), 6 rt_image_* externs (wired), full rt_cuda_* set; 3 blockers: rt_vulkan_compile_glsl has no runtime backing, Context lacks create_texture/render_pass/swapchain methods, WebGPU is pixel-upload-only (not 3D pipeline); 10 requirements drafted

### 3-arch
<pending>

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
