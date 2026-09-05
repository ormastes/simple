# Game Engine Gap Analysis: Simple vs Unity/Unreal

## Current State

The Simple engine has **117+ engine files** covering: rendering (GPU pipeline, particles, tilemap, post-processing, camera), physics (dual system with BVH+TGS/XPBD+GPU, joints, triggers, CCD, materials, collision layers), audio (miniaudio, groups, occlusion, doppler, effects), ECS, game2d framework (SDL2, assets, input, game loop), editor (panels, gizmo 2D+3D, HTML templates, undo), drawing tool (12 tools, layers, brush, rasterizer), Blink HTML engine, CC compositor, and web UI.

---

## 1. CRITICAL GAPS (Production-readiness)

| # | Feature | Description | Scope | Simple/FFI | Builds On |
|---|---------|-------------|-------|------------|-----------|
| 1 | Scene Management | Multi-scene load/unload, additive scenes, transitions | M | Simple | engine/scene/node.spl |
| 2 | Prefab System | Reusable entity templates with per-instance overrides | M | Simple | SDN serializer |
| 3 | Lighting | Directional/point/spot lights, baked/realtime | L | Simple+shader | gpu_pipeline.spl |
| 4 | Shadows | Shadow maps, cascaded shadows | L | Simple+shader | Lighting (#3) |
| 5 | Skeletal Animation | Bone hierarchy, skinned mesh, animation clips, blending | XL | Simple+FFI | glTF import (#7) |
| 6 | Animation State Machine | FSM-driven clip playback, blend trees, layers | M | Simple | common/fsm/ |
| 7 | Asset Import (glTF) | Parse glTF/GLB for meshes, materials, bones | L | Simple (FBX=FFI) | Asset system |
| 8 | Frustum Culling | Camera frustum extraction + AABB/sphere tests | M | Simple | BVH broadphase |

## 2. IMPORTANT GAPS (Feature parity)

| # | Feature | Description | Scope | Simple/FFI | Builds On |
|---|---------|-------------|-------|------------|-----------|
| 9 | NavMesh + Pathfinding | Navigation mesh generation + A* on polygons | M | Simple | graph/shortest_path |
| 10 | Character Controller | Capsule movement, slopes, steps, grounding | S | Simple | Physics2 collision |
| 11 | Object Pooling | Generic ObjectPool with acquire/release | S | Simple | particle_pool pattern |
| 12 | Coroutines | yield-per-frame workflows (wait_seconds, etc.) | S | Simple | nogc_async_mut/async |
| 13 | UI Canvas | Game-oriented screen/world-space UI, anchors, layout | L | Simple | Blink or custom |
| 14 | Shader Graph | Visual node-based shader editor | L | Simple | Blink + shader.spl |
| 15 | LOD | Distance-based mesh switching | S | Simple | renderer3d.spl |
| 16 | Render Pipeline Abstraction | Forward vs deferred, configurable passes | L | Simple | gpu_pipeline.spl |
| 17 | Profiler | CPU/GPU/memory timeline with editor integration | M | Simple+FFI | mem_tracker, editor |
| 18 | Debug Draw API | General-purpose in-game debug lines/shapes | S | Simple | physics/debug_draw |
| 19 | Skybox / Environment | Cubemap skybox, reflection probes | M | Simple+shader | Lighting (#3) |
| 20 | Sprite Atlas Packing | Auto bin-pack sprites at build time | S | Simple | sprite/atlas.spl |
| 21 | Multiplayer/Netcode | Client-server, state sync, RPCs, rollback | XL | Simple | UDP, HTTP FFI |
| 22 | Build Pipeline | Multi-platform game export + asset bundling | L | Simple | app/build |

## 3. NICE-TO-HAVE GAPS (Differentiation)

| # | Feature | Scope | Notes |
|---|---------|-------|-------|
| 23 | Ragdoll | M | Builds on existing joints system |
| 24 | IK (Inverse Kinematics) | M | Depends on skeletal anim (#5) |
| 25 | Timeline/Sequencer | L | Cinematic tool, keyframes + editor |
| 26 | Terrain/Landscape | L | Heightmap mesh, LOD, texture splatting |
| 27 | Cloth Simulation | L | GPU compute or FFI |
| 28 | Vehicle Physics | M | Specialized constraints on physics |
| 29 | Foliage/Instancing | M | GPU instanced draw calls |
| 30 | In-Game Console | S | TUI framework exists |
| 31 | Scriptable Objects | S | SDN-backed data assets |
| 32 | Visual Scripting | XL | Node graph + interpreter integration |
| 33 | Destruction System | XL | Mesh fracturing + physics |
| 34 | Audio Mixer Snapshots | S | Extends audio_group |
| 35 | HRTF Spatialization | M | miniaudio FFI extension |

---

## 4. LLM CLI INTEGRATION

**Unique differentiator** — neither Unity nor Unreal ships native LLM integration. Simple already has:
- LLM providers: Claude CLI, OpenAI API, Gemini API (`src/lib/nogc_async_mut/llm/`)
- MCP SDK: full Model Context Protocol (`src/lib/nogc_sync_mut/mcp_sdk/`)
- MCP handlers: API, debug, diagnostics (`src/lib/nogc_async_mut/mcp/handlers/`)

### LLM Features to Build

| # | Feature | What It Does | Scope |
|---|---------|-------------|-------|
| L1 | LLM CLI Command | `bin/simple editor llm "create player with physics"` → creates entities | M |
| L2 | Scene from Description | "A forest with 20 trees and a river" → generates SDN scene | S |
| L3 | Debug Assistant | "Why does player fall through floor?" → inspects physics setup | M |
| L4 | Code Generation | "Script that makes player jump on space" → valid .spl code | M |
| L5 | Asset Suggestion | "I need a jump sound" → searches asset library / HuggingFace | S |

### LLM Implementation Architecture

```
CLI dispatch → llm_command.spl
    ├── Context Packer (serializes scene/physics/assets to prompt text)
    ├── LLM Call (claude_cli.spl or openai_api.spl)
    ├── Response Parser (structured SDN/code output)
    └── Validator (parse check before applying to scene)
```

All phases are **Pure Simple** — no new C FFI required.

---

## 5. RECOMMENDED IMPLEMENTATION ORDER

### Phase 1: Core Game Framework (S/M items, high impact)
1. Scene Management (M)
2. Prefab System (M)
3. Character Controller (S)
4. Object Pooling (S)
5. Coroutines (S)
6. Debug Draw API (S)
7. In-Game Console (S)
8. Scriptable Objects (S)

### Phase 2: LLM CLI (can parallelize with Phase 3)
9. LLM CLI Command (M)
10. Scene from Description (S)
11. Debug Assistant (M)
12. Code Generation (M)
13. Asset Suggestion (S)

### Phase 3: Rendering + 3D
14. Lighting (L)
15. Shadows (L)
16. Frustum Culling (M)
17. Skybox/Environment (M)
18. LOD (S)
19. Render Pipeline Abstraction (L)

### Phase 4: Animation + AI
20. Animation State Machine (M)
21. Skeletal Animation (XL)
22. Asset Import — glTF (L)
23. NavMesh + Pathfinding (M)
24. IK (M)

### Phase 5: Tools + Polish
25. Profiler (M)
26. UI Canvas (L)
27. Shader Graph (L)
28. Sprite Atlas Packing (S)
29. Build Pipeline (L)

### Phase 6: Advanced
30. Multiplayer/Netcode (XL)
31. Ragdoll (M)
32. Timeline/Sequencer (L)
33. Terrain (L)
34. Vehicle Physics (M)
35. Foliage/Instancing (M)

---

## 6. SCORECARD

| Category | Simple | Unity | Unreal | Gap |
|----------|--------|-------|--------|-----|
| Rendering | 5 | 14 | 17 | 8-12 missing |
| Physics | 10 | 14 | 15 | 4-5 missing |
| Animation | 1 (sprite) | 4 | 5 | 3-4 missing |
| Audio | 7 | 9 | 9 | 2 missing |
| AI/Navigation | 0 | 3 | 3 | 3 missing |
| Scene/Data | 1 (basic) | 3 | 4 | 2-3 missing |
| Editor/Tools | 10 | 12 | 14 | 2-4 missing |
| Networking | 2 (raw) | 4 | 4 | 2 missing |
| **LLM/AI Assist** | **infra ready** | **0** | **0** | **Differentiator** |

**Total: ~35 features to reach Unity parity, ~45 for Unreal parity.**
**LLM CLI is a unique competitive advantage — neither Unity nor Unreal has this.**
