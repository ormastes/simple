# Simple-Native 2D Game Engine - Research Summary

**Date:** 2026-03-24
**Status:** Complete
**Related:** [Requirements](../requirement/engine_2d.md) | [Plan](../plan/engine_2d.md) | [Design](../design/engine_2d.md) | [Limitations](../bug/engine_2d_limitations.md)

---

## Executive Summary

Research evaluated existing codebase assets and external engine architectures to determine the best approach for a Simple-native 2D game engine. The conclusion: build a native engine from scratch using existing FFI bindings rather than extending the old Godot/Unreal wrapper engine. The native approach aligns with Simple's no-inheritance philosophy and produces self-contained binaries.

---

## 1. Existing Codebase Analysis

### 1.1 Old Game Engine Wrapper

The previous game engine code at `src/lib/nogc_sync_mut/game_engine/` and `test/unit/lib/game_engine/` wraps Godot and Unreal through FFI. Tests exist for scenes, shaders, materials, physics, audio, input, assets, effects, actors, and components. However, this wrapper approach:

- Requires external engine installation at runtime
- Couples Simple code to Godot/Unreal's inheritance-heavy class hierarchy
- Cannot leverage Simple's compile-time analysis for game logic

### 1.2 FFI Bindings (Reusable)

Five FFI modules were identified as directly reusable:

| FFI Module | Wraps | Reuse Status |
|-----------|-------|-------------|
| `window_ffi.spl` | Winit | Direct reuse for window management |
| `graphics2d_ffi.spl` | Softbuffer + Lyon | Direct reuse for software rendering + vector tessellation |
| `rapier2d_ffi.spl` | Rapier2D | Direct reuse for 2D physics |
| `gamepad_ffi.spl` | Gilrs | Direct reuse for gamepad input |
| `audio_ffi.spl` | Rodio | Direct reuse for audio playback |

All located in `src/lib/nogc_sync_mut/io/`.

### 1.3 Browser GPU Modules

The browser platform (`examples/browser/`) contains GPU context, device, memory, and driver modules (`src/lib/nogc_sync_mut/gpu/`, `gpu_driver/`, `gpu_runtime/`). These target a future Vulkan/WebGPU pipeline and are not needed for the initial software renderer, but inform the Phase 8 GPU acceleration design.

### 1.4 Geometry Library

`src/lib/common/geometry/` provides Point, Circle, Line, Polygon, and utility functions. These complement the engine's own `Vec2` and `Rect2` types and are available for advanced collision or path algorithms.

---

## 2. Architecture Influences

### 2.1 Godot (Scene Tree Composition)

Godot's scene tree model — where scenes are reusable node hierarchies — inspired the `Node2D` + `NodeStore` design. However, Godot relies on class inheritance (`Sprite2D extends Node2D extends CanvasItem extends Node`). Simple replaces this with composition: nodes hold data, components hold behavior, and a registry connects them.

### 2.2 Unity (Bake Pipeline)

Unity's concept of a "bake pipeline" where assets are preprocessed informed the `ResourceManager` design. Textures and audio clips are loaded once, stored by handle, and referenced cheaply by ID. The generational handle pattern comes from the Rust game engine ecosystem (Bevy, hecs).

### 2.3 Unreal (Metadata/Reflection)

Unreal's reflection and metadata system inspired the use of typed enums (`Component2D`) as a lightweight alternative. Instead of runtime reflection to query components, Simple uses exhaustive pattern matching on the enum.

---

## 3. Key Decisions

### 3.1 Native Engine vs Wrapper

**Decision:** Native engine.
**Rationale:** Wrappers impose external toolchain dependencies, force inheritance patterns incompatible with Simple, and prevent compile-time optimization of game logic. A native engine produces a single binary with all game code analyzable by the Simple compiler.

### 3.2 Software Renderer First

**Decision:** CPU-based software renderer before GPU.
**Rationale:** Zero driver dependencies, works everywhere, trivially debuggable (inspect pixel buffer directly), and sufficient for 2D games at moderate resolutions. GPU acceleration (Phase 8) can be added later behind the same `RenderCommand` interface.

### 3.3 Composition Over Inheritance

**Decision:** Enum-based components, no class hierarchy.
**Rationale:** Simple does not support class inheritance. Composition via `ComponentRegistry` + `Component2D` enum is idiomatic, type-safe, and exhaustive at compile time.

### 3.4 Fixed Timestep with Variable Rendering

**Decision:** Fixed-rate physics/logic updates, variable-rate rendering.
**Rationale:** Fixed timestep prevents physics instability from frame rate variation. Variable rendering maximizes visual smoothness. This is the standard game loop pattern (Gaffer on Games).

---

## 4. FFI Reuse Analysis

All FFI modules wrap C/Rust libraries via `extern fn` declarations. The engine modules call these directly:

```
PhysicsWorld2D  -->  rapier2d_ffi  -->  Rapier2D (Rust)
InputManager    -->  window_ffi    -->  Winit (Rust) + gamepad_ffi --> Gilrs (Rust)
AudioManager    -->  audio_ffi     -->  Rodio (Rust)
SoftwareRenderer -> graphics2d_ffi --> Softbuffer (Rust) + Lyon (Rust)
VectorRenderer  -->  graphics2d_ffi --> Lyon tessellation
```

No new FFI modules were needed for the core engine. Future work (image loading, font rendering) requires new FFI modules (`image_ffi.spl`, `font_ffi.spl`).

---

## 5. Testing Strategy

### 5.1 Unit Tests (Implemented)

10 unit test files covering pure types and core abstractions:

| Test File | Covers |
|-----------|--------|
| `ids_spec.spl` | Generational handle creation, equality, generation bump |
| `math2d_spec.spl` | Vec2 arithmetic, distance, normalize, dot product |
| `color_spec.spl` | RGBA construction, named colors |
| `rect_spec.spl` | Rect2 overlap, contains, intersection |
| `signal_spec.spl` | EventBus subscribe, emit, unsubscribe |
| `resource_handle_spec.spl` | Handle generation tracking, stale detection |
| `component_registry_spec.spl` | Attach, query, remove components |
| `sprite_spec.spl` | SpriteData, atlas region lookup |
| `renderer_spec.spl` | Render command execution, pixel output |
| `scene_node_spec.spl` | Node creation, parenting, transform composition |

### 5.2 System Tests (Planned)

A `test/system/engine_2d_spec.spl` should exercise the full engine lifecycle: create engine, add nodes, step physics, render frame, verify output.

---

## 6. References

- Gaffer on Games: Fix Your Timestep - fixed-timestep game loop pattern
- Bevy ECS: Generational entity/component handles
- Godot: Scene tree composition model
- Lyon: 2D tessellation library (used via graphics2d_ffi)
- Rapier: 2D physics engine (used via rapier2d_ffi)

## Cross-References

- **Requirements:** `doc/requirement/engine_2d.md`
- **Plan:** `doc/plan/engine_2d.md`
- **Design:** `doc/design/engine_2d.md`
- **Limitations:** `doc/bug/engine_2d_limitations.md`
- **Source:** `src/lib/nogc_sync_mut/engine/`, `src/lib/common/engine/`
- **Unit Tests:** `test/unit/lib/engine/`
- **Demo:** `examples/engine_2d_demo/main.spl`
