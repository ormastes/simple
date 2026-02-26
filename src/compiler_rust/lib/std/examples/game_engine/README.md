# Game Engine Integration Examples

This directory contains example applications demonstrating the 3D Game Engine Integration features.

## Examples

### 1. platformer_demo.spl (7.8 KB) - Cross-Engine Platformer

A simple 2D platformer game that demonstrates:

- **Cross-Engine Scene Graph**: Uses `SceneNode` trait to work with both Godot and Unreal
- **Actor Model**: Game entities managed with message-passing concurrency
- **Effect System**: Async-safe game logic with effect tracking
- **Input Abstraction**: Cross-platform input handling
- **Physics Abstraction**: Collision detection and gravity simulation
- **Audio Abstraction**: Sound effect playback

**Features:**
- Player movement (left/right)
- Jumping with gravity
- Collectible items with scoring
- Enemy patrol AI
- Effect-safe audio playback

**Running:**
```bash
# Standalone (interpreter)
./target/debug/simple simple/examples/game_engine/platformer_demo.spl
```

### 2. fps_demo_unreal.spl (12.5 KB) - Unreal Engine FPS

A 3D first-person shooter demonstrating Unreal-specific features:

- **RHI Rendering**: Direct access to Rendering Hardware Interface
- **Blueprint Integration**: Call Blueprint functions and events from Simple
- **Live Coding**: Hot-reload Simple code without restarting
- **Tick System**: Per-frame updates with tick groups
- **Editor Properties**: Expose Simple variables to Unreal Editor
- **Advanced Graphics**: Custom post-processing and rendering

**Features:**
- First-person camera with mouse look
- WASD movement and jumping
- Weapon shooting with raycasting
- Enemy AI with patrol/chase/attack states
- Blueprint integration for effects and animations
- Live coding for rapid iteration

**Running:**
```bash
# Requires Unreal Engine with Simple plugin
./target/debug/simple simple/examples/game_engine/fps_demo_unreal.spl --engine=unreal
```

### 3. rpg_demo_godot.spl (11.2 KB) - Godot Engine RPG

A 2D role-playing game demonstrating Godot-specific features:

- **Node System**: Godot's scene tree and node hierarchy
- **Signal System**: Event-driven programming with signals
- **Resource Loading**: Load sprites, tilesets, audio dynamically
- **Animation Player**: Character animations and sprite sheets
- **UI System**: Godot's Control nodes with themes
- **Inventory & Quests**: Full RPG systems

**Features:**
- Player character with stats (health, mana, level, experience)
- Movement and combat (physical attack, magic spells)
- NPC interaction and dialogue
- Inventory system with items (weapons, armor, potions, quest items)
- Quest system with objectives and rewards
- Level-up system with stat progression
- UI panels for health/mana, inventory, and quest log

**Running:**
```bash
# Requires Godot Engine with GDExtension
./target/debug/simple simple/examples/game_engine/rpg_demo_godot.spl --engine=godot
```

### 4. physics_playground.spl (10.8 KB) - Physics Simulation

A physics sandbox demonstrating the physics abstraction:

- **Rigid Body Dynamics**: Dynamic, static, and kinematic bodies
- **Collision Shapes**: Spheres, boxes, capsules, convex hulls
- **Forces & Impulses**: Apply forces, impulses, and torque
- **Collision Detection**: Broad-phase and narrow-phase collision
- **Raycasting**: Cast rays and detect hits
- **Fixed Timestep**: Deterministic physics simulation

**Demos:**
- **Bouncing Spheres**: Multiple spheres with different restitution
- **Stacking Boxes**: Physics-based box stacking with friction
- **Explosive Force**: Radial impulse explosion effect
- **Raycasting**: Target detection with ray queries

**Running:**
```bash
# Standalone (works with any engine)
./target/debug/simple simple/examples/game_engine/physics_playground.spl
```

## Common Interface Benefits

All examples use the **Common Game Engine Interface**, which means:

1. **Write Once, Run Anywhere**: Same code works with Godot or Unreal
2. **Type Safety**: Compile-time checks prevent common errors
3. **Engine Agnostic**: Switch engines without rewriting game logic
4. **Performance**: Zero-cost abstractions with direct FFI calls
5. **Hot-Reload**: Live Coding support for rapid iteration

## Architecture

```
Player (Simple Code)
       ↓
Common Interface Traits (SceneNode, Input, Physics, etc.)
       ↓
Engine-Specific Adapters
       ↓
Godot GDExtension FFI  OR  Unreal UObject FFI
       ↓
Game Engine
```

## Next Steps

To build your own game:

1. **Choose your abstractions**: Pick from 10 common interface modules
2. **Implement game logic**: Use Simple's actor model for concurrency
3. **Add effects tracking**: Ensure async safety with the effect system
4. **Test cross-engine**: Verify your game works with both engines
5. **Deploy**: Package with either Godot or Unreal

See the [Complete Guide](../../doc/report/GAME_ENGINE_PHASE2_3_COMPLETION_2025-12-27.md) for full details!
