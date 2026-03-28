# Simple-Native 2D Game Engine - Design

**Status:** Approved
**Date:** 2026-03-24
**Related:** [Requirements](../plan/requirements/engine_2d.md) | [Plan](../plan/engine_2d.md) | [Research](../research/engine_2d.md) | [Limitations](../tracking/bug/engine_2d_limitations.md)

---

## Overview

The 2D game engine is a layered architecture where pure types (no mutation, no FFI) sit at the bottom, mutable subsystems in the middle, and the game loop at the top. All code is Simple-native with FFI only at leaf modules for hardware access.

**Architecture Note (2026-03-28):** Physics is now implemented in pure Simple (no rapier2d/Rust dependency). Windowing and framebuffer presentation use the SDL2 C runtime (`rt_sdl2_*`) instead of Rust winit. The FFI layer diagram below reflects the original design; see LIM-006 and LIM-007 in the limitations doc for resolution details.

## Architecture

```
+------------------------------------------------------------------+
|                    Game Loop (core/)                              |
|  Engine2D.create() -> GameLoop.run(engine, callbacks)            |
+------------------------------------------------------------------+
|  Scene Graph    | Components   | Physics    | Input   | Audio    |
|  (scene/)       | (component/) | (physics/) | (input/)| (audio/) |
+------------------------------------------------------------------+
|  Renderer (render/)  | Sprites (sprite/)  | Resources (resource/)|
+------------------------------------------------------------------+
|  Pure Types: Vec2, Rect2, Color, NodeId, Signal  (common/engine) |
+------------------------------------------------------------------+
|  FFI: window_ffi, graphics2d_ffi, rapier2d_ffi, audio_ffi, etc. |
+------------------------------------------------------------------+
```

Data flows downward for construction, upward for queries. The game loop drives the cycle: poll input, step physics, sync transforms, build render commands, present frame.

## Module Structure

```
src/lib/common/engine/           # Pure types (no mutation, no FFI)
    __init__.spl                 # Module root
    ids.spl                      # NodeId, TextureId, AudioClipId (generational handles)
    math2d.spl                   # Vec2 (position, direction, arithmetic)
    color.spl                    # EngineColor (RGBA, named constructors)
    rect.spl                     # Rect2 (position + size, overlap, contains)
    signal/
        __init__.spl             # Signal module root
        types.spl                # SignalType enum, Signal struct
        signal.spl               # SignalConnection, emit/subscribe helpers
        event_bus.spl            # EventBus pub-sub dispatcher

src/lib/nogc_sync_mut/engine/    # Mutable subsystems (FFI at leaves)
    mod.spl                      # Engine module documentation
    __init__.spl                 # Engine init
    resource/
        types.spl                # ResourceType enum
        handle.spl               # ResourceHandle with generation tracking
        manager.spl              # ResourceManager (textures, audio clips)
    scene/
        node.spl                 # Node2D, NodeStore, transform composition
        tree.spl                 # SceneTree traversal, reparenting
    component/
        registry.spl             # ComponentRegistry, Component2D enum
        sprite.spl               # SpriteData (texture ref, source rect, flip)
        camera.spl               # Camera2DData (viewport, zoom, rotation)
        tilemap.spl              # TileMapData (grid, tile size, collision gen)
    physics/
        types.spl                # PhysicsConfig, BodyType, ColliderShape
        world.spl                # PhysicsWorld2D (Rapier2D wrapper)
        query.spl                # Ray casts, point queries
        joints.spl               # RevoluteJoint, PrismaticJoint
        debug_draw.spl           # Physics shape visualization
    input/
        types.spl                # InputAction, ActionState, KeyCode
        input_manager.spl        # InputManager (action mapping, polling)
        default_bindings.spl     # bind_wasd_movement, bind_platformer_defaults
    audio/
        types.spl                # AudioConfig, AudioBusConfig
        audio_manager.spl        # AudioManager (bus mixing, play/stop)
    sprite/
        texture.spl              # Texture (pixel data, dimensions)
        atlas.spl                # TextureAtlas (grid regions)
        sprite.spl               # AnimatedSprite (frame sequences)
    render/
        types.spl                # RenderTarget, PixelFormat
        command.spl              # RenderCommandBuffer, RenderCommand enum
        batch.spl                # SpriteBatch (z-sorted draw list)
        material.spl             # Material2D (color, blend mode)
        pipeline.spl             # SoftwareRenderer (command execution)
        vector.spl               # VectorRenderer (Lyon tessellation)
    core/
        time.spl                 # TimeState (delta, elapsed, FPS)
        game_loop.spl            # GameLoop, GameCallbacks trait
        engine.spl               # Engine2D (top-level facade)
```

## Key Type Definitions

### Node2D (scene/node.spl)

```simple
class Node2D:
    id: NodeId
    name: text
    parent: Option<NodeId>
    children: List<NodeId>
    local_position: Vec2
    local_rotation: f64
    local_scale: Vec2
    z_index: i64
    visible: bool
```

Transforms compose: `world_position(node) = parent.world_position + rotate(node.local_position, parent.world_rotation) * parent.world_scale`.

### Component2D (component/registry.spl)

```simple
enum Component2D:
    Sprite(SpriteData)
    Camera(Camera2DData)
    TileMap(TileMapData)
    Physics(body_handle: i64, collider_handle: i64)
```

An enum-based component system. No inheritance. Each node can have multiple components looked up by `NodeId` in `ComponentRegistry`.

### SoftwareRenderer (render/pipeline.spl)

```simple
class SoftwareRenderer:
    width: i64
    height: i64
    pixel_buffer: List<i64>
    window_handle: i64
```

Processes `RenderCommand` variants (Clear, DrawRect, DrawCircle, DrawSprite, DrawPolygon, DrawLine) into a pixel buffer, then presents via `graphics2d_ffi`.

### PhysicsWorld2D (physics/world.spl)

```simple
class PhysicsWorld2D:
    world_handle: i64
    gravity: Vec2
    config: PhysicsConfig
```

Wraps Rapier2D FFI handles. Methods: `create_body`, `create_collider`, `step`, `get_body_position`, `sync_to_scene`.

### InputManager (input/input_manager.spl)

```simple
class InputManager:
    action_bindings: List<ActionBinding>
    action_states: List<ActionState>
    window_handle: i64
```

Maps key/gamepad inputs to named actions. Provides `is_action_pressed`, `is_action_just_pressed`, `is_action_just_released`, `get_action_strength`.

### AudioManager (audio/audio_manager.spl)

```simple
class AudioManager:
    buses: List<AudioBus>
    device_handle: i64
```

Bus-based mixing (master, music, sfx). Each bus has volume, mute state, and active sound handles. Methods: `play`, `stop`, `pause`, `set_bus_volume`.

### Engine2D (core/engine.spl)

```simple
class Engine2D:
    nodes: NodeStore
    components: ComponentRegistry
    physics: PhysicsWorld2D
    input: InputManager
    audio: AudioManager
    renderer: SoftwareRenderer
    resources: ResourceManager
    vector: VectorRenderer
    window_handle: i64
    event_loop_handle: i64
```

Top-level facade owning all subsystems. Created via `Engine2D.create(title, width, height)`.

## API Surface

| Module | Key Functions |
|--------|--------------|
| `Engine2D` | `create`, `create_with_config`, `create_node`, `create_sprite_node`, `destroy` |
| `NodeStore` | `add`, `get`, `remove`, `set_parent`, `world_position`, `world_rotation` |
| `ComponentRegistry` | `attach`, `get_sprite`, `get_camera`, `get_tilemap`, `remove` |
| `PhysicsWorld2D` | `create_body`, `create_collider`, `step`, `get_body_position`, `sync_to_scene` |
| `InputManager` | `bind_action`, `poll_events`, `is_action_pressed`, `is_action_just_pressed` |
| `AudioManager` | `play`, `stop`, `pause`, `set_bus_volume`, `create_bus` |
| `SoftwareRenderer` | `begin_frame`, `execute_commands`, `present` |
| `ResourceManager` | `add_texture`, `add_audio_clip`, `get_texture`, `remove_texture` |
| `GameLoop` | `run(engine, callbacks, target_fps)` |
| `EventBus` | `subscribe`, `emit`, `unsubscribe` |

## Integration Points

### Scene-Physics Sync

After `physics.step()`, `physics.sync_to_scene(nodes)` reads body positions from Rapier2D and writes them back to `Node2D.local_position` and `local_rotation`. This keeps the scene graph consistent with the simulation.

### Scene-Render Pipeline

The game loop's `on_render` callback builds a `RenderCommandBuffer`. The renderer processes commands in order: clear background, draw sprites sorted by z-index, draw debug overlays. Camera2D transforms world coordinates to screen coordinates before drawing.

### Input-Game Callbacks

`InputManager.poll_events()` runs each frame before `on_update`. The game callback reads action states (`is_action_pressed("move_left")`) and applies forces or velocities to physics bodies.

### Signal Decoupling

Subsystems communicate through `EventBus` without direct references. Example: physics collision triggers `emit("collision", payload)`, game logic subscribes to handle damage. Payloads are text-serialized due to Simple's nested closure capture limitation (LIM-007).

## Design Decisions

### Why Composition, Not Inheritance

Simple does not support class inheritance by design. Components are enum variants attached to nodes via a registry. This is explicit, type-safe, and matches Simple's trait/mixin philosophy. No `class Sprite(Node2D)`.

### Why Software Renderer First

A CPU-based renderer has zero GPU driver dependencies, works on any platform, and simplifies debugging (pixel buffer is inspectable). GPU acceleration (Vulkan) is planned for Phase 8 but is not needed for correct 2D game logic.

### Why Generational Handles

Raw pointers or indices become dangling when resources are freed. Generational handles (`ResourceHandle` with `id` + `generation`) detect stale references at query time and return `nil` instead of corrupted data.

### Why Enum-Based Components

An `enum Component2D` with variants (Sprite, Camera, TileMap, Physics) is exhaustive and pattern-matchable. Adding a new component type is a single enum variant addition. This avoids the open-world problem of trait-object registries while keeping the code simple.

## Cross-References

- **Requirements:** `doc/plan/requirements/engine_2d.md`
- **Plan:** `doc/plan/engine_2d.md`
- **Research:** `doc/research/engine_2d.md`
- **Limitations:** `doc/tracking/bug/engine_2d_limitations.md`
- **Source:** `src/lib/nogc_sync_mut/engine/`, `src/lib/common/engine/`
- **Unit Tests:** `test/unit/lib/engine/`
- **Demo:** `examples/engine_2d_demo/main.spl`
