# Game Engine SceneNode Specification
*Source:* `test/feature/usage/scene_node_spec.spl`
**Feature IDs:** #GE-002  |  **Category:** Stdlib  |  **Status:** Implemented

## Overview



## Overview
SceneNode trait using math.Transformd for transform hierarchy.

## Key Concepts
| Concept | Description |
|---------|-------------|
| SceneNode | Trait for scene graph nodes |
| Transformd | f64 transform (position, rotation, scale) |

## Behavior
- SceneNode trait defines transform, hierarchy, naming, visibility
- Uses math.Transformd instead of tuple-based Transform3D
- Trait-only design (no FFI adapters)

## Feature: SceneNode Transform Integration

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | Transformd works as scene node transform | pass |
| 2 | Transformd supports position, rotation, scale | pass |
| 3 | Transformd converts to matrix for rendering | pass |

**Example:** Transformd works as scene node transform
    Given val t = math.Transformd.identity()
    Then  expect t.position.is_zero() == true
    Then  expect t.rotation.w == 1.0
    Then  expect t.scale.x == 1.0

**Example:** Transformd supports position, rotation, scale
    Given val pos = math.Vec3d(10.0, 20.0, 30.0)
    Given val rot = math.Quatd.identity()
    Given val scl = math.Vec3d(2.0, 2.0, 2.0)
    Given val t = math.Transformd(position: pos, rotation: rot, scale: scl)
    Then  expect t.position.x == 10.0
    Then  expect t.scale.x == 2.0

**Example:** Transformd converts to matrix for rendering
    Given val t = math.Transformd(
    Given val m = t.to_mat4()
    Then  expect m.data[12] == 5.0


