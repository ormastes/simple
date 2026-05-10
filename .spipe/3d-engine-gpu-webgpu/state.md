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
- [ ] 2-research (Analyst)
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
<pending>

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
