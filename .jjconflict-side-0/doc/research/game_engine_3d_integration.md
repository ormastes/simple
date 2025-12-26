# 3D Game Engine Integration Research

**Date:** 2025-12-26
**Status:** Research Complete
**Target Engines:** Godot 4.3+, Unreal Engine 5.4+

## Executive Summary

This document outlines the research for integrating Simple language with modern 3D game engines (Godot and Unreal). The goal is to create a unified interface that allows game developers to write game logic in Simple while leveraging the engine's rendering, physics, and tooling capabilities.

**Key Findings:**
- Both engines support C/C++ extension APIs suitable for FFI
- Common abstractions possible: scene graphs, components, signals/events
- Simple's unique features (actors, effects, Vulkan) provide advantages
- Godot should be implemented first (simpler API, better hot-reload)

---

## 1. Godot Engine (Version 4.3+)

### 1.1 GDExtension API

**Architecture:**
- GDExtension is Godot 4's new native extension system (replaces GDNative)
- Pure C API that can be wrapped by any language
- No recompilation of engine needed
- Hot-reload support built-in

**Key Components:**
```c
// Core GDExtension entry points
GDExtensionInitialization initialization = {
    .minimum_initialization_level = GDEXTENSION_INITIALIZATION_CORE,
    .initialize = initialize_simple_module,
    .deinitialize = uninitialize_simple_module,
};

// Class registration
godot_register_class(&class_info);
godot_register_class_method(&method_info);
godot_register_class_property(&property_info);
```

**Scene Tree & Node System:**
- Everything is a `Node` (tree hierarchy)
- Nodes have virtual functions: `_ready()`, `_process(delta)`, `_physics_process(delta)`
- Parent-child relationships with signals for events
- Scene files (.tscn) describe node hierarchies

**Signals (Event System):**
```gdscript
# Godot signals
signal health_changed(new_health)
signal player_died()

# Connect in Simple:
connect("health_changed", handler_fn)
emit_signal("health_changed", 75)
```

**Resource Management:**
- Reference counted resources (Ref<T>)
- Garbage collection for unreferenced resources
- Resource loader for async loading
- Built-in types: Texture2D, Mesh, Material, etc.

### 1.2 Rendering Pipeline

**Compositor Architecture (Godot 4.3+):**
- Vulkan-based (also OpenGL/Metal backends)
- Forward+ and Clustered Forward rendering
- Compositor nodes for custom rendering
- Direct Vulkan interop possible

**Integration Points:**
```simple
# Simple can provide custom render passes
class CustomRenderPass:
    fn render(viewport: Viewport, render_data: RenderData):
        # Access Vulkan resources directly
        vulkan_cmd_buffer = render_data.get_command_buffer()
        # Use Simple's Vulkan 2D capabilities
        draw_custom_ui(vulkan_cmd_buffer)
```

### 1.3 Physics Integration

**PhysicsServer3D API:**
- Rigid bodies, collision shapes, joints
- RayCast, ShapeCast
- Direct access to physics state
- Fixed timestep `_physics_process()`

### 1.4 Example: Godot-Rust (gdext)

The Rust `gdext` library provides excellent reference:
```rust
// Rust equivalent - Simple would be similar
#[derive(GodotClass)]
#[class(base=Node3D)]
struct Player {
    base: Base<Node3D>,
    speed: f32,
}

#[godot_api]
impl Player {
    #[func]
    fn _ready(&mut self) {
        // Initialization
    }

    #[func]
    fn _process(&mut self, delta: f64) {
        // Frame update
    }
}
```

**Simple Translation:**
```simple
@[GodotClass(base: Node3D)]
class Player:
    speed: Float32 = 5.0

    @[gdextend_func]
    fn _ready():
        print("Player ready!")

    @[gdextend_func]
    fn _process(delta: #Duration):
        # Simple's actor model for concurrent updates
        self.speed += delta.to_seconds()
```

---

## 2. Unreal Engine (Version 5.4+)

### 2.1 Module & Plugin System

**Unreal Build Tool (UBT):**
- Modules are the building blocks
- `.Build.cs` files define dependencies
- Automatic header scanning (Unreal Header Tool - UHT)
- Supports third-party language modules

**Plugin Structure:**
```
SimplePlugin/
├── SimplePlugin.uplugin          # Plugin descriptor
├── Source/
│   ├── SimplePlugin/
│   │   ├── Private/              # Implementation
│   │   ├── Public/               # Headers
│   │   └── SimplePlugin.Build.cs # Build rules
│   └── SimpleRuntime/            # Separate module for runtime
└── Content/                      # Assets
```

### 2.2 Actor/Component Architecture

**UObject System:**
- Everything inherits from `UObject`
- Reflection system (UCLASS, UPROPERTY, UFUNCTION macros)
- Garbage collection
- Serialization built-in

**Actor Model:**
```cpp
// Unreal C++ - Simple would generate similar
UCLASS()
class ASimpleActor : public AActor {
    GENERATED_BODY()

    UPROPERTY(EditAnywhere, BlueprintReadWrite)
    float Speed;

    UFUNCTION(BlueprintCallable)
    void MoveForward(float Amount);

    virtual void Tick(float DeltaTime) override;
};
```

**Simple Integration:**
```simple
@[UClass]
class SimpleActor(AActor):
    @[UProperty(EditAnywhere, BlueprintReadWrite)]
    speed: Float32 = 5.0

    @[UFunction(BlueprintCallable)]
    fn move_forward(amount: Float32):
        add_actor_local_offset(Vector3(amount * speed, 0, 0))

    fn tick(delta_time: #Duration):
        # Called every frame
        pass
```

### 2.3 Rendering (RHI - Rendering Hardware Interface)

**RHI Abstraction:**
- Unified API over D3D11/12, Vulkan, Metal
- Command lists and render passes
- Custom render passes via scene view extensions

**Vulkan Backend Access:**
```simple
# Simple can access underlying Vulkan resources
fn custom_render_pass(rhi_cmd_list: RHICommandList):
    if rhi_cmd_list.is_vulkan():
        vulkan_cmd = rhi_cmd_list.as_vulkan()
        # Use Simple's Vulkan capabilities
        simple_vulkan.draw_2d_overlay(vulkan_cmd)
```

### 2.4 Blueprint Integration

**Blueprint Virtual Machine:**
- Bytecode interpreter for visual scripting
- C++ functions can be called from Blueprints
- Events, delegates, timers

**Simple-Blueprint Bridge:**
```simple
@[BlueprintCallable]
fn calculate_damage(base_damage: Int32, multiplier: Float32) -> Int32:
    return (base_damage as Float32 * multiplier) as Int32

# Can be called from Blueprint visual scripts
```

### 2.5 Hot Reload

**Unreal's Hot Reload:**
- Live coding (Ctrl+Alt+F11)
- Recompiles changed modules
- Patches running game

**Simple Integration:**
- Watch `.spl` files for changes
- Recompile to `.smf` modules
- Load new bytecode into running game
- Simpler than C++ (no object layout changes)

---

## 3. Common Interface Design

### 3.1 Core Abstractions

**Scene Graph Unification:**
```simple
# Common interface for both engines
trait SceneNode:
    fn add_child(child: SceneNode)
    fn remove_child(child: SceneNode)
    fn get_parent() -> Option<SceneNode>
    fn update(delta: #Duration)
    fn ready()

# Godot implementation
class GodotNode(SceneNode):
    native: GodotNativeNode
    # ... implement trait methods

# Unreal implementation
class UnrealActor(SceneNode):
    native: AActor*
    # ... implement trait methods
```

**Component Pattern:**
```simple
trait Component:
    fn on_attach(node: SceneNode)
    fn on_detach()
    fn update(delta: #Duration)

class TransformComponent(Component):
    position: Vector3
    rotation: Quaternion
    scale: Vector3

class MeshComponent(Component):
    mesh: MeshResource
    materials: Array<MaterialResource>
```

### 3.2 Material & Shader System

**Unified Shader Interface:**
```simple
struct MaterialProperties:
    base_color: Color
    metallic: Float32
    roughness: Float32
    emissive: Color
    normal_map: Option<Texture>

class Material:
    properties: MaterialProperties

    # Engine-specific compilation
    fn compile_for_godot() -> GodotMaterial
    fn compile_for_unreal() -> UMaterial
```

**Custom Shaders:**
```simple
# Simple can generate GLSL/HLSL from common source
@[shader]
fn vertex_shader(input: VertexInput) -> VertexOutput:
    output.position = mvp * input.position
    output.uv = input.uv
    return output

@[shader]
fn fragment_shader(input: FragmentInput) -> Color:
    texture_color = sample_texture(base_color_tex, input.uv)
    return texture_color * tint_color
```

### 3.3 Input Handling

**Unified Input API:**
```simple
enum InputAction:
    MoveForward
    MoveRight
    Jump
    Attack

class InputManager:
    fn bind_action(action: InputAction, key: KeyCode)
    fn is_action_pressed(action: InputAction) -> Bool
    fn get_action_strength(action: InputAction) -> Float32

    # Engine-specific backends
    fn get_godot_input() -> InputGodot
    fn get_unreal_input() -> InputUnreal
```

### 3.4 Audio System

**Common Audio Interface:**
```simple
class AudioSource:
    clip: AudioClip
    volume: Float32
    pitch: Float32
    loop: Bool
    spatial: Bool

    fn play()
    fn pause()
    fn stop()

# Engine-specific implementations
class GodotAudioSource(AudioSource):
    native: AudioStreamPlayer3D

class UnrealAudioSource(AudioSource):
    native: UAudioComponent*
```

### 3.5 Asset Loading

**Async Asset System:**
```simple
# Leverages Simple's actor model
actor AssetLoader:
    fn load_mesh(path: String) -> Future<MeshResource>
    fn load_texture(path: String) -> Future<TextureResource>
    fn load_material(path: String) -> Future<MaterialResource>

# Usage with Simple's async
async fn load_player_model():
    mesh = await AssetLoader.load_mesh("res://models/player.mesh")
    texture = await AssetLoader.load_texture("res://textures/player.png")
    return PlayerModel(mesh, texture)
```

---

## 4. Simple Language Unique Features

### 4.1 Vulkan 2D Integration

**Direct Vulkan Access:**
```simple
# Simple's existing Vulkan 2D capabilities
import simple.gpu.vulkan2d

class CustomRenderer:
    vulkan_ctx: Vulkan2DContext

    fn render_overlay(engine_cmd_buffer: VkCommandBuffer):
        # Can use Simple's Vulkan 2D while engine renders 3D
        vulkan_ctx.begin_2d_pass(engine_cmd_buffer)
        vulkan_ctx.draw_rect(Rect(0, 0, 100, 100), Color.Red)
        vulkan_ctx.draw_text("Score: 100", Vector2(10, 10))
        vulkan_ctx.end_2d_pass()
```

**Benefits:**
- Zero-copy UI rendering on top of 3D scene
- Custom post-processing effects
- Debug visualization

### 4.2 Actor Model for Game Logic

**Concurrent Game Systems:**
```simple
# Each game system is an actor - true parallelism
actor AISystem:
    entities: Array<Entity>

    fn update(delta: #Duration):
        # AI can run in parallel with other systems
        for entity in entities:
            calculate_ai_decision(entity)
            send_move_command(entity)

actor PhysicsSystem:
    fn update(delta: #Duration):
        # Physics isolated from AI
        update_physics_world(delta)

# Main game loop coordinates
async fn game_loop():
    loop:
        delta = measure_frame_time()

        # Systems update in parallel!
        ai_future = AISystem.update(delta)
        physics_future = PhysicsSystem.update(delta)

        await ai_future
        await physics_future
```

**Advantages:**
- True multi-core game logic
- No manual threading
- Message passing prevents data races

### 4.3 Effect System for Safety

**Async/Sync Boundary Control:**
```simple
# Mark what code can do
@[effect(async)]
fn load_level(name: String):
    # Can use await, actors
    level_data = await AssetLoader.load(name)
    return level_data

@[effect(sync)]
fn calculate_damage(base: Int32, mult: Float32) -> Int32:
    # Cannot use await - guaranteed synchronous
    return (base as Float32 * mult) as Int32

# Godot/Unreal callbacks marked appropriately
@[effect(sync)]  # _process must be sync
fn _process(delta: #Duration):
    # Simple prevents accidental awaits here
    update_transform(delta)
```

### 4.4 Reference Capabilities for Memory Safety

**Safe Game Object References:**
```simple
# Isolated reference - exclusive access
fn create_enemy() -> iso Enemy:
    enemy = iso Enemy()
    enemy.setup()
    return enemy

# Mutable reference - shared but controlled
class GameWorld:
    enemies: Array<mut Enemy>

    fn update():
        for enemy in enemies:
            enemy.update()  # mut access safe

# Immutable reference - safe sharing
fn calculate_spawn_point(level: Level) -> Vector3:
    # Level is immutable - can't modify
    return level.spawn_points[0]
```

**Benefits:**
- Compile-time prevention of dangling pointers
- No GC overhead for game logic
- Clear ownership semantics

### 4.5 Unit Types for Physics

**Type-Safe Physical Quantities:**
```simple
# Simple's unit system for game physics
fn apply_force(body: RigidBody, force: #Force):
    # #Force = Newton (kg⋅m/s²)
    body.add_force(force)

fn set_velocity(body: RigidBody, vel: #Velocity):
    # #Velocity = m/s
    body.velocity = vel

# Compile-time unit checking
let force: #Force = 100.0#N
let mass: #Mass = 10.0#kg
let acceleration = force / mass  # Type: #Acceleration (m/s²)

# Cannot mix units incorrectly
body.add_force(mass)  # ERROR: Expected #Force, got #Mass
```

---

## 5. Implementation Strategy

### 5.1 Phase 1: Godot Integration (Months 1-3)

**Why Godot First:**
- Simpler C API (no UHT complexity)
- Better hot-reload support
- Smaller scope for validation
- Strong indie/hobbyist community

**Milestones:**
1. **M1.1:** GDExtension FFI bindings generator
   - Parse GDExtension JSON API description
   - Generate Simple FFI declarations
   - Handle variant conversions

2. **M1.2:** Node class wrapping
   - Wrap Node, Node2D, Node3D
   - Signal connect/emit
   - Virtual method overrides

3. **M1.3:** Resource system
   - Ref<T> wrapper
   - Resource loading
   - Type-safe resource handles

4. **M1.4:** Build system integration
   - SCons integration
   - Auto-compile .spl → .smf → .so
   - Hot-reload on file change

5. **M1.5:** Example game
   - Simple 2D platformer
   - Demonstrates node hierarchy
   - Uses Simple actors for game logic

### 5.2 Phase 2: Common Interface (Months 4-5)

**Extract Common Patterns:**
1. Identify common abstractions from Godot impl
2. Design trait-based interface
3. Refactor Godot impl to use common traits
4. Document engine-agnostic API

**Deliverables:**
- `simple/std_lib/src/game_engine/` module
- Common scene graph API
- Common component system
- Input/Audio abstractions

### 5.3 Phase 3: Unreal Integration (Months 6-9)

**Building on Common Interface:**
1. **M3.1:** UBT/Plugin integration
   - Generate .Build.cs
   - Simple → C++ header generation (for UHT)
   - Module system mapping

2. **M3.2:** UObject/Actor wrapping
   - AActor base class wrapper
   - UPROPERTY/UFUNCTION bindings
   - Blueprint callable functions

3. **M3.3:** Component model
   - UActorComponent wrapper
   - Tick/lifecycle integration

4. **M3.4:** RHI integration
   - Vulkan backend detection
   - Custom render passes
   - Simple Vulkan 2D overlay

5. **M3.5:** Example game
   - 3D shooter or RPG
   - Blueprint + Simple hybrid
   - Demonstrates actor model parallelism

### 5.4 FFI Binding Generation

**Automated Binding Pipeline:**
```bash
# Godot
simple-bindgen --engine godot \
    --api-json extension_api.json \
    --output simple/std_lib/src/godot/bindings/

# Unreal
simple-bindgen --engine unreal \
    --module-path Engine/Source/Runtime \
    --output simple/std_lib/src/unreal/bindings/
```

**Binding Generator Features:**
- Parse C++ headers / JSON API descriptions
- Generate Simple FFI declarations
- Create type-safe wrappers
- Handle callbacks and virtual methods
- Generate documentation

### 5.5 Hot Reload Architecture

**File Watcher:**
```simple
# Built into Simple compiler
actor FileWatcher:
    watched_paths: Array<String>

    fn watch(path: String):
        watched_paths.push(path)

    fn on_file_changed(path: String):
        # Recompile changed file
        compile_result = Compiler.compile(path)

        # Send to engine loader
        EngineLoader.reload_module(compile_result.smf_path)
```

**Engine Integration:**
- Godot: Use GDExtension's built-in reload
- Unreal: Hook into Live Coding system
- Preserve object state across reloads

### 5.6 Debugging Support

**Debug Adapter Protocol (DAP):**
```simple
# simple/app/dap/ already exists - extend for engines

class EngineDebugAdapter:
    fn set_breakpoint(file: String, line: Int32)
    fn continue()
    fn step_over()
    fn get_call_stack() -> Array<StackFrame>

    # Engine-specific variable inspection
    fn inspect_godot_node(node: Node) -> VariableTree
    fn inspect_unreal_actor(actor: AActor*) -> VariableTree
```

**Visual Debuggers:**
- VS Code extension (using DAP)
- Godot editor integration (custom dock)
- Unreal editor integration (custom tab)

---

## 6. Comparison with Other Language Bindings

### 6.1 Godot-Rust (gdext)

**Similarities:**
- FFI-based approach
- Procedural macros for boilerplate (#[GodotClass])
- Type-safe wrappers

**Simple Advantages:**
- Actor model for better parallelism
- Effect system for async safety
- Vulkan 2D for custom rendering
- Faster iteration (no Cargo rebuild times)

**Godot-Rust Advantages:**
- More mature ecosystem
- Cargo package manager integration
- Strong type system (Rust's borrow checker)

### 6.2 Unreal + Rust

**Existing Approaches:**
- Rust plugins via C++ FFI
- Limited ecosystem
- Mostly for backend services

**Simple Advantages:**
- Purpose-built for game logic
- Unit types for physics
- Better async/await story
- Simpler learning curve than Rust

### 6.3 Zig Game Engine Bindings

**Zig's Approach:**
- Direct C interop (no FFI translation)
- Comptime for zero-cost abstractions
- Good fit for engine integration

**Simple's Differentiators:**
- Higher-level abstractions (actors, effects)
- Reference capabilities for safety
- Built-in async/await
- Better for gameplay programmers (vs. engine programmers)

---

## 7. Vulkan 2D Use Cases

### 7.1 UI Overlays

**Problem:** Game engines have heavyweight UI systems
**Solution:** Simple's Vulkan 2D for lightweight, custom UI

```simple
import simple.gpu.vulkan2d

class GameHUD:
    vulkan_ctx: Vulkan2DContext

    fn render(cmd_buffer: VkCommandBuffer):
        # After engine renders 3D scene, render 2D HUD
        vulkan_ctx.begin_pass(cmd_buffer)

        # Health bar
        render_bar(Vector2(10, 10), health / max_health, Color.Red)

        # Minimap (custom render target)
        render_minimap(Vector2(900, 10), 100, 100)

        # Text (using signed distance field fonts)
        vulkan_ctx.draw_text(f"Score: {score}", Vector2(10, 50))

        vulkan_ctx.end_pass()
```

### 7.2 Debug Visualization

**Problem:** Runtime debug info difficult to visualize
**Solution:** Immediate-mode debug rendering

```simple
class DebugRenderer:
    fn draw_line(start: Vector3, end: Vector3, color: Color)
    fn draw_sphere(center: Vector3, radius: Float32, color: Color)
    fn draw_text_3d(pos: Vector3, text: String)

    # Uses Vulkan 2D for efficient batch rendering
    fn flush_to_vulkan(cmd_buffer: VkCommandBuffer):
        for line in debug_lines:
            project_to_screen(line.start, line.end)
            vulkan_ctx.draw_line_2d(screen_start, screen_end, line.color)
```

### 7.3 Custom Post-Processing

**Problem:** Engine post-processing limited
**Solution:** Custom Vulkan compute shaders

```simple
@[compute_shader]
fn custom_bloom(input_image: Texture2D, output_image: mut Texture2D):
    # Simple's GPU shader DSL
    coord = get_global_invocation_id()

    # Bright pass
    color = sample(input_image, coord)
    brightness = dot(color.rgb, Vector3(0.299, 0.587, 0.114))

    if brightness > threshold:
        output_image[coord] = color
    else:
        output_image[coord] = Color.Black
```

---

## 8. Challenges & Mitigations

### 8.1 Object Lifetime Management

**Challenge:** Game engines have their own GC/ref-counting
**Mitigation:**
- Wrap engine objects with ref-counted handles
- Use Simple's `iso`/`mut` for owned objects
- Clear ownership rules in documentation

```simple
# Engine object - ref-counted by engine
struct GodotNodeHandle:
    native_ptr: *Node
    ref_count: shared Int32  # Synced with engine

    fn drop():
        godot_object_unref(native_ptr)

# Simple object - owned by Simple
iso class GameLogic:
    data: Array<Int32>
    # Simple's GC manages this
```

### 8.2 Callback Marshalling

**Challenge:** Engine calls C++ callbacks, need Simple functions
**Mitigation:**
- Generate thunk functions in C
- Use Simple's FFI callback support
- Handle exceptions safely

```c
// Generated C thunk
void simple_node_process_callback(void* instance, double delta) {
    // Marshal to Simple
    SimpleFunctionPtr fn = get_simple_callback(instance);
    SimpleValue args[] = { simple_float64(delta) };

    // Call Simple function
    SimpleValue result = simple_call_function(fn, args, 1);

    // No return value for _process
}
```

### 8.3 Build System Complexity

**Challenge:** Integrating with SCons (Godot) and UBT (Unreal)
**Mitigation:**
- Provide pre-built plugins for common configs
- Document custom build steps
- Automate via `simple build` command

### 8.4 API Surface Size

**Challenge:** Godot/Unreal have massive APIs
**Mitigation:**
- Phase 1: Core classes only (Node, Actor, basic components)
- Generate bindings on-demand
- Community contributions for advanced features
- Focus on common interface, not 100% coverage

### 8.5 Version Compatibility

**Challenge:** Engine APIs change between versions
**Mitigation:**
- Version-specific binding generation
- Feature flags for different engine versions
- Maintain compatibility matrix
- Automated CI testing against multiple versions

---

## 9. Performance Considerations

### 9.1 FFI Call Overhead

**Measurements:**
- Modern FFI: ~1-5ns per call
- Godot virtual function: ~10-20ns
- Simple function call: ~2-3ns

**Optimization:**
- Batch operations where possible
- Use Simple's JIT for hot paths
- Profile and optimize critical paths

### 9.2 Memory Allocation

**Strategy:**
- Use engine's allocators for engine objects
- Use Simple's GC for game logic objects
- Minimize cross-boundary allocations

```simple
# Engine allocator for engine objects
let node = godot_alloc_node("Node3D")

# Simple GC for game data
let game_state = GameState {
    enemies: Array::new(),  # Simple heap
    score: 0,
}
```

### 9.3 Multi-threading

**Godot:**
- Main thread + worker threads
- Simple actors map to worker threads

**Unreal:**
- Task graph system
- Simple actors can wrap UnrealTasks

```simple
# Godot worker thread
async fn ai_worker():
    loop:
        task = await AITaskQueue.dequeue()
        result = calculate_ai(task)
        send_result(result)

# Unreal task
actor UnrealWorker:
    fn schedule_task(task: AITask):
        # Wrap in Unreal task system
        unreal_task = UnrealTask::create(|| {
            calculate_ai(task)
        })
        task_graph.add_task(unreal_task)
```

---

## 10. Documentation & Examples

### 10.1 Getting Started Guide

**Godot:**
```markdown
# Getting Started with Simple in Godot

## 1. Install Simple compiler
$ cargo install simple-lang

## 2. Create GDExtension project
$ simple new --template godot-extension my_game

## 3. Write your first node
# scripts/player.spl
@[GodotClass(base: CharacterBody3D)]
class Player:
    fn _process(delta: #Duration):
        print(f"Delta: {delta}")

## 4. Build and run
$ simple build
$ godot --path .
```

### 10.2 Example Projects

1. **2D Platformer (Godot)**
   - Character controller
   - Tilemap interaction
   - Simple actor for enemy AI

2. **3D Shooter (Unreal)**
   - First-person controller
   - Weapon system
   - Multiplayer actor replication

3. **Puzzle Game (Both)**
   - Demonstrates common interface
   - Same game logic, different engines

### 10.3 API Reference

**Generated Docs:**
```bash
$ simple doc --engine godot
# Generates HTML docs for Godot bindings

$ simple doc --engine unreal
# Generates HTML docs for Unreal bindings
```

---

## 11. Community & Ecosystem

### 11.1 Package Registry

**simple-pkg.io:**
- Host engine bindings as packages
- Version management
- Example projects

```toml
# simple.toml
[dependencies]
godot = "4.3"  # or "latest"

[dev-dependencies]
godot-test-utils = "0.1"
```

### 11.2 IDE Support

**VS Code Extension:**
- Syntax highlighting for `.spl`
- Autocomplete for engine APIs
- Inline documentation from engine
- Jump to definition (cross-language)

**Godot Editor Plugin:**
- Simple script inspector
- Live code editing
- Integrated debugger

**Unreal Editor Plugin:**
- Blueprint node generation from Simple
- Property inspector
- Hot reload UI

---

## 12. Conclusion & Recommendations

### Recommended Implementation Order:

1. **Phase 1: Godot Core (3 months)**
   - GDExtension FFI bindings
   - Node wrapping
   - Basic 2D game example

2. **Phase 2: Common Interface (2 months)**
   - Extract common patterns
   - Design trait-based API
   - Documentation

3. **Phase 3: Unreal Core (3 months)**
   - UBT integration
   - Actor/Component wrapping
   - Basic 3D game example

4. **Phase 4: Advanced Features (ongoing)**
   - Vulkan 2D integration
   - Advanced actor patterns
   - Performance optimization

### Success Metrics:

- Compile-time safety (zero UB)
- Hot reload < 1 second
- FFI overhead < 10% vs native
- Developer satisfaction (survey)
- Example game performance matches native

### Next Steps:

1. Validate approach with Godot prototype
2. Gather community feedback
3. Refine common interface design
4. Begin Phase 1 implementation
