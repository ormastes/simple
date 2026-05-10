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
- [x] 3-arch (Architect) — 2026-05-10
- [x] 4-spec (QA Lead) — 2026-05-10
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
spec-done

## Log
- 1-dev (2026-05-10): Created state file with 10 acceptance criteria, 6 parallel workstreams
- 2-research (2026-05-10): Found 32 existing files across gc_async engine3d + nogc engine render; identified 8 rt_webgpu_* externs (wired), 18 rt_vulkan_* compute externs (declared, no graphics), 6 rt_image_* externs (wired), full rt_cuda_* set; 3 blockers: rt_vulkan_compile_glsl has no runtime backing, Context lacks create_texture/render_pass/swapchain methods, WebGPU is pixel-upload-only (not 3D pipeline); 10 requirements drafted
- 3-arch (2026-05-10): Designed 16 modules (12 new files + 4 modified files across 6 disjoint streams), 8 ADR-style decisions, dependency map verified cycle-free, all 10 ACs covered, AnyRenderBackend3D tagged enum as Engine3D polymorphism boundary, ShaderCompiler decoupled from backends via PipelineDesc3D artifact handoff
- 4-spec (2026-05-10): Created 7 spec files with ~121 total it blocks, 100% AC coverage (AC-8 audit-only); Stream D split into gpu_mesh3d_spec.spl (AC-3) and gpu_lighting3d_spec.spl (AC-4); all specs use SoftwareRenderBackend3D as test backend; all specs fail (no implementation exists); placed in test/lib/nogc_sync_mut/engine/render/

### 3-arch

## Architecture

### Module Plan

All paths are relative to `src/lib/nogc_sync_mut/engine/render/` unless otherwise noted.

| Module | Path (from src/lib/nogc_sync_mut/) | Role | Stream | New/Modified |
|--------|-------------------------------------|------|--------|--------------|
| Handle types + RenderBackend3D trait | `engine/render/backend3d.spl` | Opaque handle types, PipelineDesc3D, AnyRenderBackend3D tagged enum, trait definition | A | New |
| RenderCapability3D | `engine/render/capability3d.spl` | Feature-flag struct + factory fns + detect_best_backend() | A | New |
| SoftwareRenderBackend3D | `engine/render/software_backend3d.spl` | Wraps ForwardRenderer3D via composition; implements RenderBackend3D | A | New |
| VulkanRenderBackend3D | `engine/render/vulkan_backend3d.spl` | Records VulkanCommand3D, submits via rt_vulkan_* graphics externs; extern fn declarations | B | New |
| VulkanCommand3D enum | `engine/render/vulkan_commands.spl` | Tagged command-buffer enum (no deps on other new modules) | B | New |
| WebGpuRenderBackend3D | `engine/render/webgpu_backend3d.spl` | Records WebGpuCommand3D, submits via rt_wgpu_* 3D externs; extern fn declarations | C | New |
| WebGpuCommand3D enum | `engine/render/webgpu_commands.spl` | Tagged command-buffer enum (no deps on other new modules) | C | New |
| GpuMesh3D | `engine/render/gpu_mesh3d.spl` | MeshData → vertex/index buffer upload + draw dispatch via RenderBackend3D | D | New |
| GpuLighting3D | `engine/render/gpu_lighting3d.spl` | LightUniform layout + uniform buffer upload + bind via RenderBackend3D | D | New |
| gpu_bridge.spl update | `engine/render/gpu_bridge.spl` | Wire GpuRenderState to RenderBackend3D handles; remove Context stub calls | D | Modified |
| ShaderCompiler | `engine/render/shader_compile.spl` | GLSL→SPIR-V and GLSL→WGSL compilation cache; extern rt_vulkan_compile_glsl declaration | E | New |
| WgslEmitter | `engine/render/wgsl_emitter.spl` | Token-level GLSL→WGSL transpiler; text in, text out; no new-module deps | E | New |
| shader.spl update | `engine/render/shader.spl` | Wire ShaderSource through ShaderCompiler; fill ShaderProgram.handle with real artifact | E | Modified |
| TextureCache3D | `engine/render/texture3d.spl` | GPU texture upload via RenderBackend3D; id-keyed cache replacing gpu_texture_cache stubs | F | New |
| TextureAtlas3D | `engine/render/texture_atlas3d.spl` | Atlas bin-packing + UV rect lookup; depends on texture3d.spl | F | New |
| material3d.spl update | `engine/render/material3d.spl` | Map Material3D.albedo_texture id → TextureHandle; pipeline state bind helper | F | Modified |

**File-scope enforcement:** No two streams touch the same file. `gpu_bridge.spl` → D only. `shader.spl` → E only. `material3d.spl` → F only. `engine3d.spl` and `game_loop3d.spl` are NOT modified by any stream — they reference `AnyRenderBackend3D` from `backend3d.spl` at call sites only.

---

### Opaque Handle Types (defined in backend3d.spl, imported by all other new files)

```spl
class PipelineHandle:
    id: i64
    static fn invalid() -> PipelineHandle

class BufferHandle:
    id: i64
    static fn invalid() -> BufferHandle

class TextureHandle:
    id: i64
    static fn invalid() -> TextureHandle

class RenderPassHandle:
    id: i64
    static fn invalid() -> RenderPassHandle
```

All three backends return the same handle types. Vulkan/WebGPU backends maintain internal parallel-array maps `id → native_handle: i64`. Software backend maps `id → CPU buffer index`.

---

### RenderBackend3D Trait API (backend3d.spl)

Pattern: `trait GameBackend` in `game2d/backend/trait.spl` — standalone `impl <Class>: RenderBackend3D` blocks at each backend's declaration site.

```spl
class PipelineDesc3D:
    vertex_shader_spirv: [u8]
    fragment_shader_spirv: [u8]
    vertex_shader_wgsl: text
    fragment_shader_wgsl: text
    vertex_stride: i64
    cull_back_faces: bool
    depth_write: bool
    depth_test: bool

enum TextureFormat3D:
    Rgba8Unorm
    Rgba8Srgb
    R8Unorm
    Depth32Float

trait RenderBackend3D:
    fn capabilities(self) -> RenderCapability3D
    fn init(self, width: i64, height: i64) -> bool
    fn create_pipeline(self, desc: PipelineDesc3D) -> PipelineHandle
    fn create_vertex_buffer(self, byte_count: i64) -> BufferHandle
    fn create_index_buffer(self, byte_count: i64) -> BufferHandle
    fn create_uniform_buffer(self, byte_count: i64) -> BufferHandle
    fn upload_buffer(self, buf: BufferHandle, data: [u8], offset: i64)
    fn create_texture(self, width: i64, height: i64, format: TextureFormat3D) -> TextureHandle
    fn upload_texture(self, tex: TextureHandle, data: [u8])
    fn begin_frame(self)
    fn begin_render_pass(self, color_tex: TextureHandle, depth_tex: TextureHandle) -> RenderPassHandle
    fn set_pipeline(self, pass: RenderPassHandle, pipeline: PipelineHandle)
    fn bind_vertex_buffer(self, pass: RenderPassHandle, buf: BufferHandle, slot: i64)
    fn bind_index_buffer(self, pass: RenderPassHandle, buf: BufferHandle)
    fn bind_texture(self, pass: RenderPassHandle, tex: TextureHandle, slot: i64)
    fn bind_uniform_buffer(self, pass: RenderPassHandle, buf: BufferHandle, slot: i64)
    fn draw_indexed(self, pass: RenderPassHandle, index_count: i64, base_vertex: i64)
    fn end_render_pass(self, pass: RenderPassHandle)
    fn end_frame(self)
    fn present(self)
    fn shutdown(self)

# Tagged-enum wrapper — allows Engine3D outer layer to hold any backend without boxing
enum AnyRenderBackend3D:
    Software(SoftwareRenderBackend3D)
    Vulkan(VulkanRenderBackend3D)
    WebGpu(WebGpuRenderBackend3D)
```

`AnyRenderBackend3D` is the polymorphism boundary. `Engine3D` stores one field of this type. All dispatch goes through match + trait call.

---

### RenderCapability3D (capability3d.spl)

Pattern: `SkCapability` in `skia/capability.spl` — plain class + factory fns, no methods except to_string.

```spl
enum RenderBackendKind3D:
    Software
    Vulkan
    WebGpu

class RenderCapability3D:
    backend: RenderBackendKind3D
    supports_compute_shaders: bool
    supports_msaa: bool
    supports_mip_maps: bool
    max_texture_size: i64
    max_color_attachments: i64
    supports_wgsl: bool

fn capability_software_3d() -> RenderCapability3D
fn capability_vulkan_3d() -> RenderCapability3D
fn capability_webgpu_3d() -> RenderCapability3D
fn detect_best_backend_3d() -> RenderBackendKind3D
    # calls rt_vulkan_is_available(), rt_webgpu_is_available() — falls back to Software
```

---

### SoftwareRenderBackend3D (software_backend3d.spl) — AC-9

```spl
class SoftwareRenderBackend3D:
    renderer: ForwardRenderer3D    # composition — renderer3d.spl is NOT modified
    cap: RenderCapability3D
    # CPU buffer store: buf_ids: [i64], buf_data: [[u8]]   (parallel arrays)
    # CPU texture store: tex_ids: [i64], tex_data: [[u8]], tex_widths: [i64], tex_heights: [i64]
    next_id: i64

impl SoftwareRenderBackend3D: RenderBackend3D
    # upload_buffer → copies into buf_data at matching id
    # draw_indexed  → decodes vertex/index data from CPU store, calls renderer rasterize path
    # GPU-only ops (compute) → no-op with # TODO: software backend does not support compute
```

`ForwardRenderer3D` is wrapped, never extended. Zero lines changed in `renderer3d.spl`.

---

### VulkanRenderBackend3D (vulkan_backend3d.spl + vulkan_commands.spl) — B

```spl
# vulkan_commands.spl — pure enum, no deps
enum VulkanCommand3D:
    BeginRenderPass { color_image: i64, depth_image: i64 }
    SetPipeline { pipeline_id: i64 }
    BindVertexBuffer { buffer_id: i64, slot: i64 }
    BindIndexBuffer { buffer_id: i64 }
    BindTexture { image_id: i64, slot: i64 }
    BindUniformBuffer { buffer_id: i64, slot: i64 }
    DrawIndexed { index_count: i64, base_vertex: i64 }
    EndRenderPass

# vulkan_backend3d.spl — graphics externs (new; compute externs stay in ffi_vulkan.spl)
extern fn rt_vulkan_init_graphics(width: i64, height: i64) -> i64
extern fn rt_vulkan_create_graphics_buffer(byte_count: i64, usage: i64) -> i64
extern fn rt_vulkan_upload_graphics_buffer(handle: i64, data: [u8], offset: i64)
extern fn rt_vulkan_create_image(width: i64, height: i64, format: i64) -> i64
extern fn rt_vulkan_upload_image(handle: i64, data: [u8])
extern fn rt_vulkan_create_graphics_pipeline(spirv_vert: [u8], spirv_frag: [u8], stride: i64) -> i64
extern fn rt_vulkan_begin_graphics_frame()
extern fn rt_vulkan_begin_render_pass(color: i64, depth: i64) -> i64
extern fn rt_vulkan_end_render_pass(pass: i64)
extern fn rt_vulkan_cmd_set_pipeline(pass: i64, pipeline: i64)
extern fn rt_vulkan_cmd_bind_vertex_buffer(pass: i64, buf: i64, slot: i64)
extern fn rt_vulkan_cmd_bind_index_buffer(pass: i64, buf: i64)
extern fn rt_vulkan_cmd_bind_texture(pass: i64, image: i64, slot: i64)
extern fn rt_vulkan_cmd_bind_uniform_buffer(pass: i64, buf: i64, slot: i64)
extern fn rt_vulkan_cmd_draw_indexed(pass: i64, index_count: i64, base_vertex: i64)
extern fn rt_vulkan_end_graphics_frame()
extern fn rt_vulkan_graphics_present()
extern fn rt_vulkan_shutdown_graphics()

class VulkanRenderBackend3D:
    cmds: [VulkanCommand3D]
    cap: RenderCapability3D
    # handle maps: pipeline_ids: [i64], pipeline_native: [i64]  (parallel arrays per resource type)
    next_id: i64

impl VulkanRenderBackend3D: RenderBackend3D
    # records commands into cmds[]
    # end_frame() drains cmds[] and calls rt_vulkan_cmd_* externs
```

Note: existing `rt_vulkan_*` compute externs in `gc_async_mut/gpu/engine2d/ffi_vulkan.spl` are separate and untouched. New graphics externs use `rt_vulkan_*_graphics` names to avoid collisions.

---

### WebGpuRenderBackend3D (webgpu_backend3d.spl + webgpu_commands.spl) — C

```spl
# webgpu_commands.spl — pure enum, no deps
enum WebGpuCommand3D:
    BeginRenderPass { color_tex: i64, depth_tex: i64 }
    SetPipeline { pipeline_id: i64 }
    BindVertexBuffer { buffer_id: i64, slot: i64 }
    BindIndexBuffer { buffer_id: i64 }
    BindTexture { texture_id: i64, slot: i64 }
    BindUniformBuffer { buffer_id: i64, slot: i64 }
    DrawIndexed { index_count: i64, base_vertex: i64 }
    EndRenderPass

# webgpu_backend3d.spl — 3D-specific rt_wgpu_* externs (extend existing 2D pixel-upload surface)
extern fn rt_wgpu_3d_init(width: i64, height: i64) -> i64
extern fn rt_wgpu_3d_create_buffer(byte_count: i64, usage: i64) -> i64
extern fn rt_wgpu_3d_upload_buffer(handle: i64, data: [u8], offset: i64)
extern fn rt_wgpu_3d_create_texture(width: i64, height: i64, format: i64) -> i64
extern fn rt_wgpu_3d_upload_texture(handle: i64, data: [u8])
extern fn rt_wgpu_3d_create_pipeline(wgsl_vert: text, wgsl_frag: text) -> i64
extern fn rt_wgpu_3d_begin_frame()
extern fn rt_wgpu_3d_begin_render_pass(color: i64, depth: i64) -> i64
extern fn rt_wgpu_3d_end_render_pass(pass: i64)
extern fn rt_wgpu_3d_cmd_set_pipeline(pass: i64, pipeline: i64)
extern fn rt_wgpu_3d_cmd_bind_vertex_buffer(pass: i64, buf: i64, slot: i64)
extern fn rt_wgpu_3d_cmd_bind_index_buffer(pass: i64, buf: i64)
extern fn rt_wgpu_3d_cmd_bind_texture(pass: i64, tex: i64, slot: i64)
extern fn rt_wgpu_3d_cmd_bind_uniform_buffer(pass: i64, buf: i64, slot: i64)
extern fn rt_wgpu_3d_cmd_draw_indexed(pass: i64, index_count: i64, base_vertex: i64)
extern fn rt_wgpu_3d_end_frame()
extern fn rt_wgpu_3d_present()
extern fn rt_wgpu_3d_shutdown()

class WebGpuRenderBackend3D:
    cmds: [WebGpuCommand3D]
    cap: RenderCapability3D
    next_id: i64

impl WebGpuRenderBackend3D: RenderBackend3D
    # identical command-buffer record/drain pattern as Vulkan
```

Existing `rt_webgpu_*` (2D pixel-upload) externs in `engine2d/backend_webgpu.spl` are untouched. New 3D externs use `rt_wgpu_3d_*` prefix. Rust runtime stubs are added to `src/runtime/hosted/webgpu.rs` by Stream C.

---

### GPU Mesh Pipeline (gpu_mesh3d.spl) — D, AC-3

Data flow:
```
MeshData { vertices: [f32], indices: [u32] }
  → gpu_mesh_upload(backend: RenderBackend3D, mesh: MeshData) -> GpuMeshHandle
       backend.create_vertex_buffer(vertex_byte_count)
       backend.upload_buffer(vbuf, raw_f32_bytes, 0)
       backend.create_index_buffer(index_byte_count)
       backend.upload_buffer(ibuf, raw_u32_bytes, 0)

  → gpu_mesh_draw(backend, pass, handle, mvp_buf, pipeline)
       backend.bind_vertex_buffer(pass, vbuf, 0)
       backend.bind_index_buffer(pass, ibuf)
       backend.bind_uniform_buffer(pass, mvp_buf, 0)   # MVP 4x4 f32 column-major
       backend.draw_indexed(pass, index_count, 0)
```

```spl
class GpuMeshHandle:
    vbuf: BufferHandle
    ibuf: BufferHandle
    index_count: i64
    static fn invalid() -> GpuMeshHandle

fn gpu_mesh_upload(backend: RenderBackend3D, vertices: [f32], indices: [u32]) -> GpuMeshHandle
fn gpu_mesh_draw(backend: RenderBackend3D, pass: RenderPassHandle, mesh: GpuMeshHandle, mvp_buf: BufferHandle, pipeline: PipelineHandle)
fn gpu_mesh_free(handle: GpuMeshHandle)   # marks handles invalid; GPU resource lifetime managed by backend
```

MVP matrix (16 f32, 64 bytes) is computed by Engine3D outer layer (MDSOC policy), uploaded to `mvp_buf` before draw. GPU vertex shader reads from uniform binding slot 0.

---

### GPU Lighting Pipeline (gpu_lighting3d.spl) — D, AC-4

```spl
class LightUniform:
    position_x: f32
    position_y: f32
    position_z: f32
    light_type: i64     # 0=directional 1=point 2=spot
    color_r: f32
    color_g: f32
    color_b: f32
    intensity: f32

class GpuLightingState:
    light_buf: BufferHandle
    max_lights: i64
    light_count: i64

fn gpu_lighting_init(backend: RenderBackend3D, max_lights: i64) -> GpuLightingState
fn gpu_lighting_upload(state: GpuLightingState, backend: RenderBackend3D, lights: [LightUniform])
fn gpu_lighting_bind(state: GpuLightingState, backend: RenderBackend3D, pass: RenderPassHandle)
    # binds to uniform slot 1 (slot 0 = MVP)
```

Fragment shader reads lights from binding slot 1. Software backend decodes LightUniform from CPU buffer and passes to ForwardRenderer3D existing Phong path.

---

### Shader Pipeline (shader_compile.spl + wgsl_emitter.spl) — E, AC-5

Data flow:
```
ShaderSource { glsl_vertex: text, glsl_fragment: text }
  → shader_compiler_get_or_compile_spirv(compiler, src) -> ShaderArtifact
       hash = hash_text(src.glsl_vertex + src.glsl_fragment)
       cache lookup → miss → rt_vulkan_compile_glsl(text, stage) -> [u8]
       returns ShaderArtifact { spirv_vertex, spirv_fragment, is_compiled }

  → shader_compiler_get_or_compile_wgsl(compiler, src) -> ShaderArtifact
       hash = same key
       cache lookup → miss → WgslEmitter.emit(glsl_text) -> text
       returns ShaderArtifact { wgsl_vertex, wgsl_fragment, is_compiled }
```

```spl
class ShaderArtifact:
    spirv_vertex: [u8]
    spirv_fragment: [u8]
    wgsl_vertex: text
    wgsl_fragment: text
    is_compiled: bool
    error_msg: text

class ShaderCache:
    keys: [i64]         # hash keys (parallel array)
    artifacts: [ShaderArtifact]

class ShaderCompiler:
    cache: ShaderCache

fn shader_compiler_new() -> ShaderCompiler
fn shader_compiler_get_or_compile_spirv(compiler: ShaderCompiler, src: ShaderSource) -> ShaderArtifact
fn shader_compiler_get_or_compile_wgsl(compiler: ShaderCompiler, src: ShaderSource) -> ShaderArtifact

# Extern — declared here; backing symbol added to src/runtime/hosted/ by Stream E
extern fn rt_vulkan_compile_glsl(source: text, stage: i64) -> [u8]
    # stage: 0=vertex 1=fragment; returns SPIR-V bytes; empty [] on failure

class WgslEmitter:    # in wgsl_emitter.spl
    # stateless; pure text→text

fn wgsl_emit_vertex(glsl: text) -> text
fn wgsl_emit_fragment(glsl: text) -> text
```

Backends do NOT import `shader_compile.spl`. They receive pre-compiled `PipelineDesc3D { spirv_vertex, wgsl_vertex, ... }` from the Engine3D outer (policy) layer. This severs the E→B/C dependency.

---

### Texture / Material Pipeline (texture3d.spl + texture_atlas3d.spl) — F, AC-7

Data flow:
```
rt_image_load(path) -> pixel handle: i64
  → texture_cache_upload(cache, backend, width, height, format, pixel_bytes) -> texture_id: i64
       backend.create_texture(w, h, format)
       backend.upload_texture(handle, data)
       store handle at texture_id

Material3D { albedo_texture: TextureId }
  → material_bind(mat, cache, backend, pass)
       h = texture_cache_get(cache, mat.albedo_texture.id)
       backend.bind_texture(pass, h, 0)   # albedo = slot 0
       backend.bind_texture(pass, normal_h, 1) if has normal
       backend.set_pipeline(pass, pipeline_for_mat_type(mat.mat_type))
```

```spl
class TextureCache3D:
    ids: [i64]
    handles: [TextureHandle]
    widths: [i64]
    heights: [i64]
    next_id: i64

fn texture_cache_new() -> TextureCache3D
fn texture_cache_upload(cache: TextureCache3D, backend: RenderBackend3D, width: i64, height: i64, format: TextureFormat3D, data: [u8]) -> i64
fn texture_cache_get(cache: TextureCache3D, id: i64) -> TextureHandle
fn texture_cache_evict(cache: TextureCache3D, id: i64)

class AtlasRect:
    x: i64
    y: i64
    width: i64
    height: i64
    u0: f32
    v0: f32
    u1: f32
    v1: f32

class TextureAtlas3D:
    atlas_texture: TextureHandle
    rects: [AtlasRect]
    ids: [i64]
    atlas_width: i64
    atlas_height: i64

fn atlas_new(backend: RenderBackend3D, width: i64, height: i64) -> TextureAtlas3D
fn atlas_pack(atlas: TextureAtlas3D, backend: RenderBackend3D, id: i64, data: [u8], w: i64, h: i64) -> AtlasRect
fn atlas_lookup(atlas: TextureAtlas3D, id: i64) -> AtlasRect

# material3d.spl additions (existing file, stream F only):
fn material_bind(mat: Material3D, cache: TextureCache3D, backend: RenderBackend3D, pass: RenderPassHandle)
fn pipeline_for_mat_type(mat_type: Material3DType) -> PipelineHandle   # lookup from Engine3D pipeline cache
```

---

### Dependency Map

```
backend3d.spl          → (no deps on other new modules; defines base types only)
capability3d.spl       → backend3d.spl (RenderBackendKind3D)
software_backend3d.spl → backend3d.spl, capability3d.spl, engine/render/renderer3d.spl (ForwardRenderer3D)
vulkan_commands.spl    → (no deps; pure enum)
vulkan_backend3d.spl   → backend3d.spl, capability3d.spl, vulkan_commands.spl
webgpu_commands.spl    → (no deps; pure enum)
webgpu_backend3d.spl   → backend3d.spl, capability3d.spl, webgpu_commands.spl
gpu_mesh3d.spl         → backend3d.spl
gpu_lighting3d.spl     → backend3d.spl
gpu_bridge.spl (mod)   → backend3d.spl, gpu_mesh3d.spl, gpu_lighting3d.spl
wgsl_emitter.spl       → (no deps on new modules; text → text)
shader_compile.spl     → engine/render/shader.spl (ShaderSource only), wgsl_emitter.spl
shader.spl (mod)       → shader_compile.spl
texture3d.spl          → backend3d.spl
texture_atlas3d.spl    → texture3d.spl, backend3d.spl
material3d.spl (mod)   → texture3d.spl, backend3d.spl

Cycle check:
  B/C (vulkan/webgpu backends) do NOT import shader_compile.spl — they consume ShaderArtifact bytes
  via PipelineDesc3D passed in by the Engine3D outer layer. E has no dependency on B or C.
  F does not import D. D does not import E or F.
  No circular dependencies: verified.
```

---

### Architecture Decisions

- **D-1: RenderBackend3D as trait with standalone impl blocks, not enum dispatch** — Context: need polymorphism across 3 backends without inheritance. Decision: `trait RenderBackend3D` + `impl <Class>: RenderBackend3D` at each backend site, exactly matching `GameBackend` in `game2d/backend/trait.spl`. Consequences: new backends (Metal, OpenGL) can be added without touching the trait file; all backends are independently testable.

- **D-2: Opaque i64-wrapped handle types (PipelineHandle, BufferHandle, TextureHandle, RenderPassHandle)** — Context: three backends have incompatible native handle types (VkPipeline, WGPURenderPipeline, CPU array index). Decision: all wrapped as `class X { id: i64 }`. Each backend keeps internal parallel-array id→native maps. Consequences: trait methods unify across all backends; no backend leaks its native type into the trait surface.

- **D-3: Command-buffer recording, not immediate-mode submission** — Context: Skia `VkCommand` enum is proven in this codebase. Decision: Vulkan/WebGPU backends accumulate tagged enums in `cmds: []`, drain on `end_frame()`. Software backend executes immediately (no buffering overhead). Consequences: enables validation, deferred execution, and future command reuse without changing the trait.

- **D-4: ShaderCompiler decoupled from backends — artifacts only at pipeline creation** — Context: if backends import `shader_compile.spl`, E→B/C creates a cycle or forces serial implementation. Decision: Engine3D outer (MDSOC policy) layer calls `shader_compiler_get_or_compile_*()` before calling `backend.create_pipeline(desc)`. Backends receive `PipelineDesc3D { spirv_vertex: [u8], wgsl_vertex: text }` — compiled artifacts, not source. Consequences: E depends on nothing in B/C; B/C depend on nothing in E; shader cache lives in policy layer.

- **D-5: SoftwareRenderBackend3D wraps ForwardRenderer3D via composition, no modification to renderer3d.spl** — Context: AC-9 requires zero regression on existing CPU rasterizer. Decision: `SoftwareRenderBackend3D` holds `renderer: ForwardRenderer3D` as a value field; draw_indexed decodes vertex/index from CPU buffer store and calls existing renderer path. Consequences: `renderer3d.spl` (555 lines) is not touched by any stream.

- **D-6: New graphics externs use distinct name prefixes to avoid collision with existing compute externs** — Context: `rt_vulkan_*` compute externs already declared in `gc_async_mut/gpu/engine2d/ffi_vulkan.spl`; `rt_webgpu_*` 2D externs already in `engine2d/backend_webgpu.spl`. Decision: new 3D Vulkan graphics externs use `rt_vulkan_*_graphics` or `rt_vulkan_cmd_*` variants; WebGPU 3D externs use `rt_wgpu_3d_*` prefix. All new extern declarations start with `is_compiled: false` stubs. Consequences: no naming collision; existing code compiles unchanged.

- **D-7: MDSOC+ boundary — Engine3D outer layer owns all policy decisions, ECS business layer holds only data** — Context: AC-8. Decision: `Engine3D` (outer/policy) holds `AnyRenderBackend3D`, `ShaderCompiler`, `TextureCache3D`, `GpuLightingState`; it calls `begin_frame/end_frame/present`. `ComponentRegistry3D`, `NodeStore3D` (business layer) hold no references to any `backend3d.spl` types. No business-layer file imports `backend3d.spl`. Consequences: business layer remains pure data; Engine3D orchestrates all GPU resource lifecycle.

- **D-8: AnyRenderBackend3D tagged enum as the Engine3D polymorphism boundary** — Context: Simple has no trait objects / dynamic dispatch boxes. Decision: `enum AnyRenderBackend3D { Software(SoftwareRenderBackend3D), Vulkan(VulkanRenderBackend3D), WebGpu(WebGpuRenderBackend3D) }` defined in `backend3d.spl`. Engine3D stores one field of this type; all frame calls go through `match + trait fn`. Consequences: all three backends are statically dispatched; no allocation needed; adding a 4th backend requires extending this enum only.

---

### Requirement Coverage

| AC | Module(s) |
|----|-----------|
| AC-1 (RenderBackend3D trait + 3 impls) | `backend3d.spl` (A), `software_backend3d.spl` (A), `vulkan_backend3d.spl` (B), `webgpu_backend3d.spl` (C) |
| AC-2 (RenderCapability3D + detection) | `capability3d.spl` (A) |
| AC-3 (GPU mesh pipeline) | `gpu_mesh3d.spl` (D), `gpu_bridge.spl` update (D) |
| AC-4 (GPU lighting) | `gpu_lighting3d.spl` (D) |
| AC-5 (GLSL→SPIR-V/WGSL cross-compile) | `shader_compile.spl` (E), `wgsl_emitter.spl` (E), `shader.spl` update (E) |
| AC-6 (rt_wgpu_* externs + Rust stubs) | `webgpu_backend3d.spl` extern block (C); `src/runtime/hosted/webgpu.rs` stubs (C) |
| AC-7 (3D texture system) | `texture3d.spl` (F), `texture_atlas3d.spl` (F), `material3d.spl` update (F) |
| AC-8 (MDSOC+ audit) | D-7: Engine3D outer policy; no business-layer file imports backend3d.spl |
| AC-9 (ForwardRenderer3D preserved) | `software_backend3d.spl` wraps via composition (D-5); renderer3d.spl unchanged |
| AC-10 (no inheritance, trait+composition, tagged enums) | D-1, D-3, D-5, D-8 enforced across all streams; AnyRenderBackend3D tagged enum |

### 4-spec

## Specs

### Spec Files

- `test/lib/nogc_sync_mut/engine/render/backend3d_spec.spl` — 23 specs covering AC-1, AC-2, AC-9, AC-10
- `test/lib/nogc_sync_mut/engine/render/vulkan_backend3d_spec.spl` — 17 specs covering AC-1 (Vulkan impl), AC-10
- `test/lib/nogc_sync_mut/engine/render/webgpu_backend3d_spec.spl` — 17 specs covering AC-1 (WebGPU impl), AC-6, AC-10
- `test/lib/nogc_sync_mut/engine/render/gpu_mesh3d_spec.spl` — 12 specs covering AC-3
- `test/lib/nogc_sync_mut/engine/render/gpu_lighting3d_spec.spl` — 17 specs covering AC-4
- `test/lib/nogc_sync_mut/engine/render/shader_compile_spec.spl` — 16 specs covering AC-5
- `test/lib/nogc_sync_mut/engine/render/texture3d_spec.spl` — 19 specs covering AC-7

**Total: 7 spec files, ~121 `it` blocks**

**Implementer note (enum equality):** Several specs compare tagged enum values with `==` (e.g. `cmd == VulkanCommand3D.BeginRenderPass(...)`, `cap.backend == RenderBackendKind3D.Vulkan`). Equality on data-carrying enum variants is not confirmed by existing codebase examples. The implementer for AC-1/AC-6 may need to provide `eq(other)` helpers or `kind_name() -> text` accessors and update the relevant `it` blocks accordingly. Simple enum variants without payloads (e.g. `RenderBackendKind3D.Software`) are lower risk.

### AC Coverage Matrix

| AC | Spec File | it block | Status |
|----|-----------|----------|--------|
| AC-1 | `backend3d_spec.spl` | "invalid() returns id of -1" (×4 handle types) | Failing (no impl) |
| AC-1 | `backend3d_spec.spl` | "vertex_stride field is stored" | Failing (no impl) |
| AC-1 | `backend3d_spec.spl` | "init returns true for software backend" | Failing (no impl) |
| AC-1 | `backend3d_spec.spl` | "create_vertex_buffer returns valid handle" | Failing (no impl) |
| AC-1 | `backend3d_spec.spl` | "begin_frame then end_frame does not crash" | Failing (no impl) |
| AC-1 | `vulkan_backend3d_spec.spl` | "VulkanCommand3D enum construction" (×8 variants) | Failing (no impl) |
| AC-1 | `vulkan_backend3d_spec.spl` | "create_vertex_buffer returns non-invalid handle" | Failing (no impl) |
| AC-1 | `vulkan_backend3d_spec.spl` | "full recording sequence does not crash" | Failing (no impl) |
| AC-1 | `webgpu_backend3d_spec.spl` | "WebGpuCommand3D enum construction" (×8 variants) | Failing (no impl) |
| AC-1 | `webgpu_backend3d_spec.spl` | "full recording sequence does not crash" | Failing (no impl) |
| AC-2 | `backend3d_spec.spl` | "capability_software_3d backend kind is Software" | Failing (no impl) |
| AC-2 | `backend3d_spec.spl` | "capability_vulkan_3d backend kind is Vulkan" | Failing (no impl) |
| AC-2 | `backend3d_spec.spl` | "capability_webgpu_3d backend kind is WebGpu" | Failing (no impl) |
| AC-2 | `backend3d_spec.spl` | "detect_best_backend_3d returns valid kind" | Failing (no impl) |
| AC-3 | `gpu_mesh3d_spec.spl` | "invalid() vbuf/ibuf id is -1" | Failing (no impl) |
| AC-3 | `gpu_mesh3d_spec.spl` | "vbuf id is valid after upload" | Failing (no impl) |
| AC-3 | `gpu_mesh3d_spec.spl` | "index_count equals number of indices" | Failing (no impl) |
| AC-3 | `gpu_mesh3d_spec.spl` | "gpu_mesh_draw does not crash" | Failing (no impl) |
| AC-3 | `gpu_mesh3d_spec.spl` | "after free, vbuf/ibuf ids are -1" | Failing (no impl) |
| AC-4 | `gpu_mesh3d_spec.spl` | "light_type is 0 for directional" | Failing (no impl) |
| AC-4 | `gpu_mesh3d_spec.spl` | "light_buf id is valid after init" | Failing (no impl) |
| AC-4 | `gpu_mesh3d_spec.spl` | "gpu_lighting_upload does not crash" | Failing (no impl) |
| AC-4 | `gpu_mesh3d_spec.spl` | "gpu_lighting_bind does not crash" | Failing (no impl) |
| AC-5 | `shader_compile_spec.spl` | "is_compiled is false when not compiled" | Failing (no impl) |
| AC-5 | `shader_compile_spec.spl` | "creates compiler with empty cache" | Failing (no impl) |
| AC-5 | `shader_compile_spec.spl` | "second call returns cached result (cache size stable)" | Failing (no impl) |
| AC-5 | `shader_compile_spec.spl` | "different sources produce separate cache entries" | Failing (no impl) |
| AC-5 | `shader_compile_spec.spl` | "wgsl_emit_vertex output contains @vertex" | Failing (no impl) |
| AC-5 | `shader_compile_spec.spl` | "gl_Position replaced by builtin position annotation" | Failing (no impl) |
| AC-5 | `shader_compile_spec.spl` | "wgsl_emit_fragment output contains @fragment" | Failing (no impl) |
| AC-5 | `shader_compile_spec.spl` | "gl_FragColor not present in WGSL output" | Failing (no impl) |
| AC-6 | `webgpu_backend3d_spec.spl` | "backend kind is WebGpu" | Failing (no impl) |
| AC-6 | `webgpu_backend3d_spec.spl` | "supports_wgsl is true for WebGpu" | Failing (no impl) |
| AC-6 | `webgpu_backend3d_spec.spl` | "create_pipeline returns non-invalid handle for WGSL desc" | Failing (no impl) |
| AC-7 | `texture3d_spec.spl` | "upload returns id >= 0" | Failing (no impl) |
| AC-7 | `texture3d_spec.spl` | "two uploads produce distinct ids" | Failing (no impl) |
| AC-7 | `texture3d_spec.spl` | "get returns valid handle for uploaded id" | Failing (no impl) |
| AC-7 | `texture3d_spec.spl` | "get for unknown id returns invalid handle" | Failing (no impl) |
| AC-7 | `texture3d_spec.spl` | "evict removes entry from cache" | Failing (no impl) |
| AC-7 | `texture3d_spec.spl` | "atlas pack returns rect with correct width/height" | Failing (no impl) |
| AC-7 | `texture3d_spec.spl` | "atlas lookup returns same rect as pack" | Failing (no impl) |
| AC-7 | `texture3d_spec.spl` | "material_bind does not crash with valid albedo" | Failing (no impl) |
| AC-8 | (audit-only) | MDSOC+ audit — no it block; enforced via D-7 arch constraint | Audit-only |
| AC-9 | `backend3d_spec.spl` | "init returns true for software backend" | Failing (no impl) |
| AC-9 | `backend3d_spec.spl` | "capabilities returns Software kind" | Failing (no impl) |
| AC-9 | `backend3d_spec.spl` | "upload_buffer does not panic for valid handle" | Failing (no impl) |
| AC-10 | `backend3d_spec.spl` | "Software variant holds SoftwareRenderBackend3D" | Failing (no impl) |
| AC-10 | `vulkan_backend3d_spec.spl` | command recording tests (trait+composition, no inheritance) | Failing (no impl) |
| AC-10 | `webgpu_backend3d_spec.spl` | command recording tests (trait+composition, no inheritance) | Failing (no impl) |

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
