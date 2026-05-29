# Simple-Native 2D Game Engine - Requirements

**Status:** Implementing
**Date:** 2026-03-24
**Related:** [Plan](../engine_2d.md) | [Design](../../design/engine_2d.md) | [Research](../../research/engine_2d.md) | [Limitations](../../tracking/bug/engine_2d_limitations.md)

---

## Feature Name

Simple-Native 2D Game Engine

## Motivation

The existing game engine code (`src/lib/nogc_sync_mut/game_engine/`) wraps external engines (Godot, Unreal) through FFI. This approach creates tight coupling to third-party toolchains, limits portability, and prevents the Simple compiler from reasoning about game logic at compile time. A native engine written entirely in Simple gives full control over the runtime, enables composition-based architecture aligned with Simple's design philosophy, and produces self-contained binaries with zero external engine dependencies.

## Scope

### In Scope

- 2D scene graph with parent-child transform hierarchy
- Composition-based component system (enum variants, no inheritance)
- Software 2D renderer with sprite batching and z-order sorting
- Physics integration wrapping Rapier2D via FFI
- Input system with configurable action mapping (keyboard + gamepad)
- Audio system with bus-based mixing via Rodio FFI
- Handle-based resource management with generational IDs
- Fixed-timestep game loop with frame interpolation
- Signal/event system for decoupled communication
- Texture atlas packing and animated sprites
- TileMap support with collision integration
- Camera2D with viewport projection
- Vector graphics via Lyon tessellation FFI
- Playable platformer demo example

### Out of Scope

- 3D rendering, 3D physics, 3D scene nodes
- GPU/Vulkan graphics pipeline (future Phase 8)
- Editor UI, visual scripting, property inspector
- Networking, multiplayer, replication
- Mobile and console platform targets
- Image file loading (requires `image_ffi.spl`, not yet implemented)
- Font/text rendering (requires `font_ffi.spl`, not yet implemented)

---

## Requirements

### REQ-ENG-001: Scene Graph with Node2D Hierarchy

The engine provides a `Node2D` scene graph where each node holds a local transform (position, rotation, scale). Parent transforms compose with child transforms so moving a parent moves all descendants. Nodes are stored in a flat `NodeStore` indexed by `NodeId`.

**Acceptance:** Create a parent node, attach a child, set parent position to (100, 50). Child's world position equals parent position plus child local position.

### REQ-ENG-002: Composition-Based Component System

Components attach to nodes via `ComponentRegistry`. Components are an enum (`Component2D`) with variants for Sprite, Camera, TileMap, and Physics. No class inheritance is used.

**Acceptance:** Attach a Sprite component and a Physics component to the same node. Both are retrievable by node ID.

### REQ-ENG-003: Software 2D Renderer

A `SoftwareRenderer` produces a pixel buffer each frame by processing render commands (clear, draw sprite, draw rect, draw circle, draw polygon, draw line). Sprites are z-sorted before rendering. Output goes to a Winit window surface via `graphics2d_ffi`.

**Acceptance:** Render two overlapping sprites with different z-indices. The higher-z sprite occludes the lower-z sprite.

### REQ-ENG-004: Physics Integration (Rapier2D)

`PhysicsWorld2D` wraps `rapier2d_ffi` to provide rigid bodies (static, dynamic, kinematic), colliders (box, circle), gravity, stepping, and position readback. Physics positions sync back to scene node transforms each frame.

**Acceptance:** Create a dynamic body above a static floor. After stepping, the dynamic body's y-position increases (falls toward floor).

### REQ-ENG-005: Input System with Action Mapping

`InputManager` maps raw key codes and gamepad buttons to named actions (e.g., "move_left", "jump"). Supports pressed/just-pressed/just-released queries. Default bindings provided for WASD + platformer controls.

**Acceptance:** Bind "jump" to Space key. Simulate key press. `is_action_just_pressed("jump")` returns true on first query, false on second without re-press.

### REQ-ENG-006: Audio System with Bus-Based Mixing

`AudioManager` wraps `audio_ffi` (Rodio) to play sounds on named buses (master, music, sfx). Each bus has independent volume. Supports play, stop, pause, resume, and volume control.

**Acceptance:** Play a sound on the "sfx" bus. Set sfx bus volume to 0.5. Master bus volume remains 1.0.

### REQ-ENG-007: Handle-Based Resource Management

`ResourceManager` stores textures and audio clips behind generational handles (`TextureId`, `AudioClipId`). Handles are typed wrappers around `ResourceHandle` with generation tracking to detect stale references.

**Acceptance:** Add a texture, get handle. Remove texture. Attempt access with old handle returns nil (generation mismatch).

### REQ-ENG-008: Fixed-Timestep Game Loop

`GameLoop` runs a fixed-timestep update loop (default 60 Hz) with variable-rate rendering. Provides `GameCallbacks` trait with `on_update(engine, dt)` and `on_render(engine, cmds)` hooks.

**Acceptance:** Run loop for 10 frames. `on_update` is called with consistent dt. `on_render` is called each frame.

### REQ-ENG-009: Signal/Event System

`EventBus` provides publish-subscribe communication. Signals carry a topic string and serialized text payload. Subscribers register callbacks by topic. `Signal` and `SignalType` enums define built-in event categories.

**Acceptance:** Subscribe to "player_hit" topic. Emit signal with payload "damage:10". Subscriber callback receives the payload.

### REQ-ENG-010: Texture Atlas Packing

`TextureAtlas` subdivides a texture into a grid of `AtlasRegion` entries. Each region maps to a source `Rect2`. Supports both uniform grid and manual region definitions.

**Acceptance:** Create an atlas from a 128x128 texture with 32x32 cells. Region at (1, 0) has source rect (32, 0, 32, 32).

### REQ-ENG-011: Animated Sprites

`AnimatedSprite` sequences atlas regions into named animations with configurable frame duration and looping. Advancing the animation updates the current frame index and source rect.

**Acceptance:** Create a 4-frame "walk" animation at 10 FPS. After advancing 0.1s, current frame is 1.

### REQ-ENG-012: TileMap Support

`TileMapData` stores a 2D grid of tile IDs with configurable tile size. Tiles reference atlas regions. The renderer draws visible tiles in correct z-order. Collision shapes can be generated from non-empty tiles.

**Acceptance:** Create a 10x10 tilemap with tile size 16. Set tile (2, 3) to ID 5. Query returns 5.

### REQ-ENG-013: Camera2D with Viewport Projection

`Camera2DData` defines a viewport with position, zoom, and rotation. The renderer uses the active camera to transform world coordinates to screen coordinates.

**Acceptance:** Set camera position to (100, 100) with zoom 2.0. A world-space sprite at (100, 100) renders at screen center. A sprite at (150, 100) renders at screen center + 100px (50 * 2.0 zoom).

### REQ-ENG-014: Vector Graphics (Lyon Tessellation)

`VectorRenderer` wraps `graphics2d_ffi` Lyon bindings to tessellate filled/stroked paths into triangle meshes. Supports circles, rectangles, rounded rectangles, and arbitrary paths.

**Acceptance:** Tessellate a filled circle with radius 50. Output contains vertex and index buffers with non-zero lengths.

### REQ-ENG-015: Playable Demo Example

A minimal platformer demo (`examples/engine_2d_demo/main.spl`) demonstrates engine usage: window creation, physics world setup, input binding, render loop, and player movement.

**Acceptance:** Demo compiles and runs. Player rectangle moves with WASD. Gravity pulls player down. Ground collision prevents falling through floor.

---

## Dependencies

| Module | Path | Purpose |
|--------|------|---------|
| `window_ffi` | `src/lib/nogc_sync_mut/io/window_ffi.spl` | Winit window creation |
| `graphics2d_ffi` | `src/lib/nogc_sync_mut/io/graphics2d_ffi.spl` | Software rendering + Lyon |
| `rapier2d_ffi` | `src/lib/nogc_sync_mut/io/rapier2d_ffi.spl` | Physics engine |
| `gamepad_ffi` | `src/lib/nogc_sync_mut/io/gamepad_ffi.spl` | Gilrs gamepad input |
| `audio_ffi` | `src/lib/nogc_sync_mut/io/audio_ffi.spl` | Rodio audio playback |
| `geometry` | `src/lib/common/geometry/` | Point, polygon, circle types |

## Cross-References

- **Plan:** `doc/03_plan/engine_2d.md`
- **Design:** `doc/05_design/engine_2d.md`
- **Research:** `doc/01_research/engine_2d.md`
- **Limitations:** `doc/bug/engine_2d_limitations.md`
- **Source:** `src/lib/nogc_sync_mut/engine/`, `src/lib/common/engine/`
- **Unit Tests:** `test/unit/lib/engine/`
- **Demo:** `examples/engine_2d_demo/main.spl`

## std.game2d Game Framework Layer (2026-04-25)

A LÖVE-style game framework `std.game2d` ships layered over the existing `engine/` library.

**Scope shipped:** Tier 0 (tiny: `App` trait + `Canvas` + `g.run`) and Tier 1 (asset-typed `Image`/`Sound`/`Font` handles) plus the entry of Tier 2 (`game.sdn` + `assets.sdn` SDN loaders with `GAME-ASSET-001/002/014` diagnostics). Headless backend with FNV-1a `frame_hash` for deterministic-replay/golden-frame tests, snapshot-based input, fixed-step deterministic loop with runtime `GAME-DET-001` guard, `bin/simple game new|run|test|inspect` CLI.

**Deferred (out of scope this iteration):** Tier 2 full `scene.sdn` entity tree, Tier 3 ECS, Tier 4 editor, animation, tilemap, audio mixer beyond `play(Sound)`, UI widgets, Vulkan/WebGPU backends, packaging, profiler, hot reload, compile-time `#[deterministic]` lint rule.

**Acceptance Criteria final verdicts** (full text in `.sstack/game2d-framework/state.md` `### 1-dev`):

- AC-1 App trait + `g.run` + 25-line demo — **PASS**
- AC-2 Canvas API + math re-exports — **PASS**
- AC-3 Snapshot-based input — **PASS**
- AC-4 Fixed-step + determinism runtime guard — **PASS**
- AC-5 Headless replay + golden-frame — **PARTIAL** (synthetic 4×4 hash; real-demo pin blocked by `impl X: Trait` parse + interpreter bulk-buffer limit; see follow-up tickets 3 + 4)
- AC-6 SDN `game.sdn` + `assets.sdn` + diagnostics — **PASS**
- AC-7 `bin/simple game` subcommand — **PASS**
- AC-8 `<800` LOC files, no inheritance, generics with `<>`, reuse engine primitives — **PASS**

Spec totals: 9 specs / 122 it-blocks all green; engine_2d 6/6 + primitives 3/3 regression clean.

**Related bug filed during pipeline:** `doc/08_tracking/bug/parser_member_target_in_single_line_if.md` (single-line-if member-target assignment — workaround in demo).
