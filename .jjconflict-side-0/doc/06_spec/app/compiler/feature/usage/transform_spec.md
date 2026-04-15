# Transform Specification

Transform (f32) and Transformd (f64) combining position, rotation, and scale.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MATH-004 |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/feature/usage/transform_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview
Transform (f32) and Transformd (f64) combining position, rotation, and scale.

## Key Concepts
| Concept | Description |
|---------|-------------|
| Transform | Position + rotation + scale |
| Composition | Parent-child transform combining |
| to_mat4 | Convert to 4x4 matrix |

## Behavior
- Identity transform: origin, no rotation, unit scale
- Compose transforms for hierarchy
- Convert to matrix for GPU upload
- SLERP-based interpolation

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/transform/result.json` |

## Scenarios

- creates identity transform
- converts to mat4
- identity forward is +Z
- identity right is +X
- identity up is +Y
- combines identity transforms
- combines translation
- transforms a point
- lerps between transforms
