# Simple-Native 2D Game Engine - Implementation Plan

**Status:** Implementing
**Date:** 2026-03-24
**Related:** [Requirements](requirements/engine_2d.md) | [Design](../design/engine_2d.md) | [Research](../research/engine_2d.md) | [Limitations](../tracking/bug/engine_2d_limitations.md)

---

## Summary

The engine is implemented in 8 phases with a clear dependency DAG. Phases 1 and 2 are foundational. Phases 3a, 3b, and 3c are parallelizable (physics, input, audio share no mutual dependencies). Phases 4-7 build upward. Phase 8 is future GPU work.

## Metrics

| Metric | Count |
|--------|-------|
| Source files (`.spl`) | 51 |
| Unit test files | 10 |
| System test files | 0 (planned) |
| Demo files | 1 |
| Source LOC | ~6,789 |
| Test LOC | ~911 |
| Total LOC | ~7,700 |

## Phase Breakdown

### Phase 1: Pure Types (common/engine/)

**Delivers:** Vec2, Rect2, EngineColor, NodeId/TextureId/AudioClipId, Signal/EventBus
**Files:** 9 source, 5 unit tests
**LOC:** ~526 source, ~458 test
**REQs:** REQ-ENG-007 (handles), REQ-ENG-009 (signals)

| File | LOC | Purpose |
|------|-----|---------|
| `ids.spl` | 100 | Generational handle IDs |
| `math2d.spl` | 256 | Vec2 arithmetic, distance, normalize |
| `color.spl` | 135 | RGBA color, named constructors |
| `rect.spl` | 118 | Rect2 position+size, overlap, contains |
| `signal/types.spl` | - | SignalType enum |
| `signal/signal.spl` | - | SignalConnection |
| `signal/event_bus.spl` | - | Pub-sub EventBus |

### Phase 2: Scene Graph + Components + Resources

**Delivers:** Node2D, NodeStore, SceneTree, ComponentRegistry, ResourceManager
**Depends on:** Phase 1
**Files:** 10 source, 3 unit tests
**LOC:** ~1,386 source, ~267 test
**REQs:** REQ-ENG-001 (scene graph), REQ-ENG-002 (components), REQ-ENG-007 (resources)

| File | LOC | Purpose |
|------|-----|---------|
| `scene/node.spl` | 521 | Node2D, NodeStore, transform composition |
| `scene/tree.spl` | 251 | SceneTree traversal, reparenting |
| `component/registry.spl` | 225 | ComponentRegistry, Component2D enum |
| `component/sprite.spl` | 195 | SpriteData component |
| `component/camera.spl` | 107 | Camera2DData component |
| `component/tilemap.spl` | 182 | TileMapData component |
| `resource/handle.spl` | 173 | ResourceHandle with generation |
| `resource/types.spl` | 62 | ResourceType enum |
| `resource/manager.spl` | 130 | ResourceManager |

### Phase 3a: Physics (parallel)

**Delivers:** PhysicsWorld2D, colliders, joints, debug draw
**Depends on:** Phase 1 (Vec2), Phase 2 (NodeStore for sync)
**Files:** 5 source, 1 unit test
**LOC:** ~775 source, ~(physics_spec)
**REQs:** REQ-ENG-004 (physics)

### Phase 3b: Input (parallel)

**Delivers:** InputManager, action mapping, default bindings
**Depends on:** Phase 1 (types only)
**Files:** 4 source, 1 unit test
**LOC:** ~684 source
**REQs:** REQ-ENG-005 (input)

### Phase 3c: Audio (parallel)

**Delivers:** AudioManager, bus-based mixing
**Depends on:** Phase 1 (types only)
**Files:** 3 source, 1 unit test
**LOC:** ~579 source
**REQs:** REQ-ENG-006 (audio)

### Phase 4: Sprites + Atlas

**Delivers:** Texture, TextureAtlas, AnimatedSprite
**Depends on:** Phase 1 (Rect2, ids), Phase 2 (resources)
**Files:** 4 source, 1 unit test
**LOC:** ~697 source
**REQs:** REQ-ENG-010 (atlas), REQ-ENG-011 (animated sprites)

### Phase 5: Renderer

**Delivers:** SoftwareRenderer, RenderCommand, SpriteBatch, Material2D, VectorRenderer
**Depends on:** Phase 1, Phase 2 (scene), Phase 4 (sprites)
**Files:** 7 source, 1 unit test
**LOC:** ~716 source
**REQs:** REQ-ENG-003 (renderer), REQ-ENG-013 (camera), REQ-ENG-014 (vector graphics)

### Phase 6: Game Loop + Engine2D

**Delivers:** TimeState, GameLoop, GameCallbacks, Engine2D facade
**Depends on:** All previous phases
**Files:** 4 source
**LOC:** ~494 source
**REQs:** REQ-ENG-008 (game loop)

### Phase 7: Demo + TileMap Integration

**Delivers:** Playable platformer demo, TileMap collision integration
**Depends on:** Phase 6
**Files:** 1 demo
**LOC:** ~500+ demo
**REQs:** REQ-ENG-012 (tilemap), REQ-ENG-015 (demo)

### Phase 8: GPU Acceleration (Future)

**Delivers:** Vulkan render backend, GPU sprite batching
**Depends on:** Phase 5 (renderer abstraction)
**Status:** Not started
**REQs:** None yet (new requirements needed)

## Dependency DAG

```
Phase 1 (Pure Types)
    |
    v
Phase 2 (Scene + Components + Resources)
    |         |           |
    v         v           v
Phase 3a   Phase 3b   Phase 3c
(Physics)  (Input)    (Audio)     <-- parallel
    |         |           |
    +----+----+-----------+
         |
         v
Phase 4 (Sprites + Atlas)
         |
         v
Phase 5 (Renderer)
         |
         v
Phase 6 (Game Loop + Engine2D)
         |
         v
Phase 7 (Demo + TileMap Integration)
         |
         v
Phase 8 (GPU Acceleration) [future]
```

## Cross-References

- **Requirements:** `doc/plan/requirements/engine_2d.md`
- **Design:** `doc/design/engine_2d.md`
- **Research:** `doc/research/engine_2d.md`
- **Limitations:** `doc/tracking/bug/engine_2d_limitations.md`
- **Source:** `src/lib/nogc_sync_mut/engine/`, `src/lib/common/engine/`
- **Unit Tests:** `test/unit/lib/engine/`
- **Demo:** `examples/engine_2d_demo/main.spl`
