# Game Engine SceneNode Specification

**Feature ID:** #GE-002 | **Category:** Stdlib | **Difficulty:** 2/5 | **Status:** Implemented

_Source: `test/feature/usage/scene_node_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 3 |

## Test Structure

### SceneNode Transform Integration

- ✅ Transformd works as scene node transform
- ✅ Transformd supports position, rotation, scale
- ✅ Transformd converts to matrix for rendering

