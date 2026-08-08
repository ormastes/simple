# Game Engine Enhancement Plan — 2D/3D Unification, Physics, Audio, Feature Gaps

**Date:** 2026-06-12
**Status:** Draft (research synthesis)
**Related:**
- [engine_2d plan](engine_2d.md), [engine_2d research](../../../../01_research/ui/graphics/engine_2d.md)
- [3D integration research](../../../../01_research/ui/graphics/3d/3D_GAME_ENGINE_INTEGRATION_RESEARCH.md)
- [2D render optimization (ComputeSession)](../../../compiler/backend/render_2d_optimization_plan_2026-05-30.md)
- [Engine2D CPU/Vulkan parity](engine2d_cpu_vulkan_parallel_2026-05-29.md)

## 1. Current State (verified 2026-06-12)

| Area | Status |
|------|--------|
| 2D compositor | **Layer-based.** `src/lib/nogc_sync_mut/compositor/` — `LayerTree`/`CompositeLayer` (z-index stacking), tiles, damage tracking, `gpu_surface.spl`, `gpu_command.spl`. cc/viz-style. |
| 2D game lib | `src/lib/nogc_sync_mut/game2d/` — sprite_batch, texture_atlas, canvas, font, input, asset tables. CPU/Vulkan pixel parity closed (2026-05-29). |
| 3D | `engine/render/renderer3d.spl`, gpu_mesh3d, gpu_lighting3d, gpu_particle; `gpu/engine3d/` backends (CUDA/Vulkan/ROCm/Intel/WebGPU/baremetal); `game3d_session.spl`; `engine/core/game_loop3d.spl`. |
| Audio | `engine/audio/` — manager, groups (bus-like), mixer_snapshot, effects, **HRTF, doppler, occlusion, listener_system** over vendored miniaudio. |
| Physics | `engine/physics/` — scalar+SIMD solver, simd_broadphase, bvh2d, backend_gpu, CCD, character_controller, collision_layers, solver_body3d, AoSoA data. |
| Other | animation (skeleton/IK/blender/timeline), input_manager+default_bindings, net (client/server/rpc/sync), ai/navmesh, profiler, object_pool, components (sprite/tilemap/mesh/camera/camera3d/particle), build_pipeline, llm tools. |

Compute-backend unification (CUDA/HIP/OpenCL/SIMD behind one `ComputeSession` trait) remains **Draft** in the 2026-05-30 plan — HIP/Level-Zero have no session classes; CPU "SIMD" kernels are scalar loops.

## 2. Web Research Summary (2025–2026)

### Engine architecture
- **ECS:** Industry converged on archetype-table storage (Bevy/DOTS/flecs) with opt-in sparse-set for volatile components; first-class relationships (flecs → Bevy 0.16). Scheduling: infer read/write conflicts from query signatures → auto-parallel DAG over a work-stealing pool. Fits MDSOC+ ECS business layer.
- **Rendering:** Retained render graph (DAG of typed nodes/resource slots) + extracted render world (Bevy 0.15). GPU-driven path = multi-draw-indirect + bindless + GPU cull (Bevy 0.16, Unreal RDG); CPU draw loops stop scaling ~10k objects. Keep CPU fallback.
- **Audio:** Bus-graph (FMOD/Wwise/Godot model) over miniaudio's `ma_engine` node graph; Steam Audio C API as optional HRTF/occlusion spatializer plugin via SFFI.

### 2D/3D unification — answer to "can layers merge with the 3D surface?"
**Yes — and it is the industry-standard pattern.** All major engines composite 2D as layers onto the 3D-rendered surface:
- **Godot:** 3D renders to Viewport; numbered `CanvasLayer`s composite on top (HUD ≥1, parallax ≤-1). Clearest model.
- **Unity:** camera stacking — base 3D camera + overlay ortho cameras into same render target; sorting layers within camera.
- **Bevy:** `Camera2d`/`Camera3d` target the same surface, ordered by integer `Camera.order`.
- **Pitfalls:** do NOT share a depth buffer between 2D and 3D by default (z-fighting); HUD must render at native res even when 3D is resolution-scaled; depth-interleaved 2D-in-3D needs a custom path — use render-to-texture-on-mesh (SubViewport pattern) for world-space 2D/UI.

**Design for Simple:** the existing `CompositeLayer`/`LayerTree` becomes the universal compositor. `renderer3d` output becomes one `CompositeLayer` at z-index 0 targeting the shared `gpu_surface`; game2d canvases and GUI are sibling layers above/below by z-index. Add `render_order: i64` to camera components; world-space 2D = canvas rendered to texture, sampled on a `gpu_mesh3d` mesh. This makes 2D, GUI, and 3D seamlessly one surface with no new abstraction.

### Physics
- **3D SOTA:** Jolt — 4-wide SIMD quad-tree broadphase (double-buffered), GJK/EPA narrowphase, sequential-impulse velocity + position pass, island job graph with large-island graph-coloring split, warm-start contact cache.
- **2D SOTA:** Box2D v3 — C17, solver-sets (awake/sleeping/disabled) in SoA, graph-colored contact groups, SIMD-wide solving.
- **Unified 2D+3D core is proven practical:** Rapier ships rapier2d/3d from one dimension-generic codebase; Avian (bevy_xpbd) layers XPBD + ECS adapter on Parry.
- **For Simple:** keep current `engine/physics` direction, evolve toward: dimension-generic core (`<Vec2|Vec3>` generics) sharing broadphase/islands/solver; SI + warm starting default, XPBD optional for soft constraints; determinism as compile flag (excludes SIMD/parallel, Rapier model); physics core ECS-free with a separate ECS adapter; fixed timestep + render interpolation as first-class.

### Feature-gap checklist (what's still needed for "experience libs")
Tier 1 (must-have, currently missing/partial):
1. **Input action-mapping** — logical actions bound to key/pad/touch with persisted remapping (input_manager exists; verify action layer + haptics).
2. **Asset pipeline** — offline cook to platform blobs, async streaming loader with dependency hashes, hot reload; glTF, KTX2/Basis, Ogg.
3. **Scene/prefab serialization + save games** — entity/component blueprints (SDN format), stable save-state subset.
4. **Animation state machines** — blend trees (1D/2D spaces) over existing blender/timeline; deterministic, decoupled from render tick.
5. **UI text shaping/i18n** — HarfBuzz-class shaping (bidi/CJK/emoji) over game2d font; retained HUD widgets + immediate-mode debug overlay.
6. **Frame pacing** — present-mode control (vsync/mailbox/immediate), present timing, not just FPS cap.

Tier 2: data/asset hot reload; netcode model (rollback GGRS-style for deterministic games, snapshot-interpolation otherwise — net/ has rpc/sync but no rollback); GPU particles (gpu_particle exists — wire to compute path); 2D lighting/SDF shadows; tweening lib; profiler timeline + frame debugger + crash reporting.

Tier 3: scripting/modding hooks, world-space UI, post-processing stack (bloom/tonemap/SSAO as composable passes), visual editor (top missing-feature complaint for library-style stacks).

## 4. Interface Unification (web renderers / 2D backends / GUI+TUI)

Verified 2026-06-12 — one pattern across all three tiers: shared semantic contract on top, trait-abstracted backends below, native paths may bypass a tier with typed evidence.

| Tier | Shared interface | Backends | Status |
|------|-----------------|----------|--------|
| UI (GUI+TUI+web) | `SemanticUiTree`/`SemanticUiCommand` + `draw_ir` (`src/lib/common/ui/`), UISession (`nogc_sync_mut/ui/session.spl`) | `SurfaceAdapter` → TUI, pure Simple GUI, pure Simple web, Tauri, Electron, NodeJS/browser | Designed (accelerated_shared_ui_backend_architecture.md, Active); contract not yet frozen |
| Web render | `web_render_backend.spl` shared API | Simple-native renderer **with direct Engine2D bypass** (`simple_web_engine2d_renderer.spl`, `browser_engine2d_bridge.spl`); external webviews use semantic contract only | Bypass implemented; not yet a typed capability |
| 2D engine | `RenderBackend` + `Engine2DExtended` traits (`gpu/engine2d/`) | CpuBackend, VulkanBackend (impl'd); CUDA/HIP/OpenCL/SIMD pending ComputeSession plan (Draft 2026-05-30) | Partially landed |

Gaps to close:
1. Freeze the semantic UI contract; add adapter-equivalence specs (same tree → same interaction result on TUI/GUI/web) before more host-specific behavior.
2. Formalize the native-renderer bypass: adapters expose `reached_engine2d` + fallback reason as typed results (design doc error-handling section), so the advanced path is queryable, not implicit.
3. Land ComputeSession unification so game2d, GUI, and the web renderer share the same backend traits; per-backend conformance specs with typed hardware-absent states.
4. Tie-in with P1 below: once renderer3d output is a CompositeLayer, web/GUI/TUI surfaces and 3D share one compositor and swapchain.

## 5. Proposed Phases

- **P1 Unified surface:** 3D-output-as-CompositeLayer; `render_order` on cameras; world-space canvas-to-texture. Spec: 2D HUD over rotating 3D mesh, single swapchain.
- **P2 Physics core consolidation:** dimension-generic broadphase/solver share between bvh2d and 3D path; warm-start cache; island parallelism via graph coloring; fixed-timestep + interpolation in game_loop/game_loop3d.
- **P3 Audio bus API:** named buses + sends + effect slots over audio_group; Steam Audio SFFI spike for HRTF upgrade.
- **P4 Tier-1 gaps:** asset cook/stream, scene/prefab/save serialization, animation state machines, input action remap persistence, text shaping, frame pacing.
- **P5 Render graph:** typed-DAG pass system over gpu_command; MDI+bindless on Vulkan path (depends on ComputeSession unification plan).
- **P6 Tier-2:** rollback netcode, GPU particle compute, 2D lighting, tooling.

Each phase lands with sspec coverage in interpreter mode (per compile-mode false-green rule).
