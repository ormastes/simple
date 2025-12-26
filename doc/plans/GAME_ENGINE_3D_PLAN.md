# 3D Game Engine Integration Implementation Plan

**Created:** 2025-12-26
**Status:** Planning
**Priority:** High
**Target Engines:** Godot 4.3+ → Unreal 5.4+

## Overview

Implement Simple language bindings for Godot and Unreal Engine, starting with Godot due to simpler API surface. Create a unified interface that allows both engines to be used with similar Simple code while leveraging Simple's unique features (Vulkan 2D, actors, effects, unit types).

## Goals

1. Enable game development in Simple with professional game engines
2. Provide type-safe, ergonomic APIs
3. Support hot-reload for rapid iteration
4. Leverage Simple's unique features for better game architecture
5. Create common abstraction layer for engine-agnostic code

## Phase 1: Godot Integration (3 months)

### Month 1: Foundation & FFI

**Week 1-2: Build System & GDExtension Setup**
- [ ] Research GDExtension build requirements
- [ ] Create `simple/std_lib/src/godot/` module structure
- [ ] Setup SCons integration for building `.so`/`.dll`
- [ ] Generate GDExtension entry points from Simple

**Week 3-4: FFI Binding Generator**
- [ ] Parse GDExtension `extension_api.json`
- [ ] Generate Simple FFI declarations for core classes
- [ ] Implement Variant ↔ Simple type conversion
- [ ] Handle method calls and callbacks

**Deliverable:** `simple-bindgen godot` tool that generates bindings

### Month 2: Core API Wrapping

**Week 1-2: Node System**
- [ ] Wrap `Node`, `Node2D`, `Node3D` base classes
- [ ] Implement virtual method overrides (`_ready`, `_process`, etc.)
- [ ] Support node hierarchy (add_child, get_parent)
- [ ] Handle node lifecycle

**Week 3-4: Signals & Resource System**
- [ ] Implement signal connect/emit
- [ ] Wrap `Ref<T>` for reference counting
- [ ] Resource loading (sync and async)
- [ ] Custom resource types

**Deliverable:** Working Simple game object that can be instantiated in Godot

### Month 3: Practical Features & Example

**Week 1-2: Input, Physics, Rendering**
- [ ] Input handling (keyboard, mouse, gamepad)
- [ ] Physics bodies and collision
- [ ] Sprite and mesh rendering integration
- [ ] Camera control

**Week 3-4: Example Game**
- [ ] Implement 2D platformer in Simple
- [ ] Demonstrate Simple actors for game logic
- [ ] Hot-reload support
- [ ] Documentation and tutorial

**Deliverable:** Complete "Simple Platformer" demo game

## Phase 2: Common Interface Design (2 months)

### Month 4: Interface Extraction

**Week 1-2: Core Traits**
- [ ] Design `SceneNode` trait
- [ ] Design `Component` trait
- [ ] Design `Material` and `Shader` abstractions
- [ ] Design `Input` and `Audio` abstractions

**Week 3-4: Refactor Godot Implementation**
- [ ] Refactor Godot bindings to use common traits
- [ ] Add engine-agnostic examples
- [ ] Document migration from engine-specific to common API

**Deliverable:** `simple/std_lib/src/game_engine/` common interface module

### Month 5: Vulkan 2D Integration

**Week 1-2: Compositor Integration**
- [ ] Hook into Godot compositor system
- [ ] Access Vulkan command buffers
- [ ] Render Simple Vulkan 2D on top of 3D scene

**Week 3-4: Custom Render Passes**
- [ ] Custom post-processing effects
- [ ] Debug visualization overlays
- [ ] Performance profiling UI

**Deliverable:** Example showing Vulkan 2D UI overlay on Godot 3D scene

## Phase 3: Unreal Integration (3 months)

### Month 6: Unreal Build System

**Week 1-2: UBT Integration**
- [ ] Generate `.Build.cs` files from Simple modules
- [ ] Integrate with Unreal Header Tool (UHT)
- [ ] Plugin structure (`SimplePlugin.uplugin`)
- [ ] Module dependency resolution

**Week 3-4: FFI Binding Generator**
- [ ] Parse Unreal C++ headers
- [ ] Generate Simple FFI declarations
- [ ] Handle UObject reflection macros
- [ ] Blueprint callable function generation

**Deliverable:** Simple Unreal plugin that can be loaded in editor

### Month 7: Actor/Component System

**Week 1-2: AActor Wrapping**
- [ ] Wrap `AActor` base class
- [ ] Implement Tick function
- [ ] UPROPERTY and UFUNCTION bindings
- [ ] Spawn and destroy actors

**Week 3-4: Component System**
- [ ] Wrap `UActorComponent`
- [ ] Common components (mesh, collision, movement)
- [ ] Component lifecycle management

**Deliverable:** Simple actor running in Unreal game

### Month 8: Advanced Features & Example

**Week 1-2: Blueprint Integration**
- [ ] Call Simple functions from Blueprints
- [ ] Blueprint events in Simple
- [ ] Blueprint library functions
- [ ] Property exposure to editor

**Week 3-4: Example Game**
- [ ] Implement 3D shooter or RPG mechanics
- [ ] Demonstrate actor model parallelism
- [ ] Hot-reload demonstration
- [ ] Documentation and tutorial

**Deliverable:** Complete "Simple Unreal Demo" project

## Phase 4: Polishing & Release (1 month)

### Month 9: Documentation & Tooling

**Week 1-2: Documentation**
- [ ] Complete API reference (auto-generated)
- [ ] Getting started guide for each engine
- [ ] Tutorial series (beginner → advanced)
- [ ] Best practices document
- [ ] Migration guide

**Week 3-4: Tooling & Release**
- [ ] VS Code extension updates (Godot/Unreal support)
- [ ] Debugger integration (DAP with engines)
- [ ] Performance profiling tools
- [ ] Package releases on simple-pkg.io

**Deliverable:** Public release of Simple 3D game engine support

## Technical Architecture

### Module Structure

```
simple/std_lib/src/
├── game_engine/           # Common interface
│   ├── __init__.spl
│   ├── scene.spl         # SceneNode trait
│   ├── component.spl     # Component trait
│   ├── material.spl      # Material system
│   ├── input.spl         # Input abstraction
│   └── audio.spl         # Audio abstraction
│
├── godot/                # Godot-specific
│   ├── __init__.spl
│   ├── bindings/         # Generated FFI
│   ├── node.spl          # Node wrappers
│   ├── resource.spl      # Resource system
│   ├── signals.spl       # Signal system
│   └── physics.spl       # Physics integration
│
└── unreal/               # Unreal-specific
    ├── __init__.spl
    ├── bindings/         # Generated FFI
    ├── actor.spl         # AActor wrappers
    ├── component.spl     # UActorComponent
    ├── blueprint.spl     # Blueprint integration
    └── rhi.spl           # RHI access
```

### Hot-Reload Architecture

```simple
# Watch .spl files
actor FileWatcher:
    fn watch(paths: Array<String>):
        # Monitor for changes
        pass

    fn on_change(file: String):
        # Recompile
        result = compile(file)

        # Reload in engine
        match engine:
            Engine.Godot => reload_gdextension(result.so_path)
            Engine.Unreal => reload_live_coding(result.dll_path)
```

### FFI Safety Layer

```simple
# Safe wrappers prevent UB
class GodotNode:
    native: *Node  # Raw pointer
    ref_count: Rc<Int>  # Synced with Godot

    fn call_method(name: String, args: Array<Variant>) -> Result<Variant, Error>:
        # Validate object still alive
        if !is_valid(self.native):
            return Err(Error::InvalidObject)

        # Safe FFI call with error handling
        catch_godot_error(|| {
            godot_object_call_method(self.native, name, args)
        })
```

## Dependencies

### External Libraries
- **Godot:** GDExtension SDK (header-only, included with engine)
- **Unreal:** Unreal Engine source (requires Epic Games account)
- **LibClang:** For C++ header parsing (bindgen)

### Simple Compiler Features Required
- ✅ FFI support (already complete)
- ✅ Procedural macros (for `@[GodotClass]`, etc.)
- ✅ Trait system (for common interface)
- ✅ Actor system (for game logic parallelism)
- ✅ Effect system (for async safety)

## Success Metrics

### Performance
- [ ] Hot-reload < 1 second for small changes
- [ ] FFI overhead < 5% vs native C++
- [ ] Frame time impact < 1ms for typical game logic

### Usability
- [ ] Developer can create simple game in < 1 hour
- [ ] API feels natural to both engine and Simple developers
- [ ] Error messages are clear and actionable

### Safety
- [ ] Zero segfaults in game logic code
- [ ] All engine callbacks are type-safe
- [ ] Memory leaks prevented by compiler

### Community
- [ ] 5+ community example games in first 3 months
- [ ] Positive feedback from beta testers
- [ ] Active development in both Godot and Unreal communities

## Risks & Mitigations

### Risk: Engine API Changes
**Mitigation:** Version-specific binding generation, maintain compatibility matrix

### Risk: Build System Complexity
**Mitigation:** Provide pre-built plugins for common configurations, automated build scripts

### Risk: Performance Overhead
**Mitigation:** Profile early, optimize hot paths, provide zero-cost abstractions

### Risk: Limited Ecosystem
**Mitigation:** Focus on core use cases first, enable community contributions, provide excellent documentation

## Future Enhancements (Post-Release)

- [ ] Additional engines (Unity via C#, Bevy, O3DE)
- [ ] Advanced graphics features (ray tracing, global illumination)
- [ ] Network replication integration
- [ ] Mobile platform support (Android, iOS)
- [ ] Console support (PlayStation, Xbox, Switch)
- [ ] Visual scripting integration
- [ ] Asset pipeline integration
- [ ] Profiling and debugging tools

## References

- Research: `doc/research/game_engine_3d_integration.md`
- Godot GDExtension Docs: https://docs.godotengine.org/en/stable/tutorials/scripting/gdextension/
- Unreal Plugin Docs: https://docs.unrealengine.com/5.4/en-US/plugins-in-unreal-engine/
- Rust gdext library: https://github.com/godot-rust/gdext (reference implementation)
