# Game Engine SceneNode Specification

SceneNode trait using Transformd for transform hierarchy.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GE-002 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/feature/usage/scene_node_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview
SceneNode trait using Transformd for transform hierarchy.

## Key Concepts
| Concept | Description |
|---------|-------------|
| SceneNode | Trait for scene graph nodes |
| Transformd | f64 transform (position, rotation, scale) |

## Behavior
- SceneNode trait defines transform, hierarchy, naming, visibility
- Uses Transformd instead of tuple-based Transform3D
- Trait-only design (no FFI adapters)

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/scene_node/result.json` |

## Scenarios

- Transformd works as scene node transform
- Transformd supports position, rotation, scale
- Transformd converts to matrix for rendering
