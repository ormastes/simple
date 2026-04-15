# Mat4 Specification

Mat4 (f32) and Mat4d (f64) 4x4 transformation matrices with column-major storage.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MATH-002 |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/feature/usage/mat4_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview
Mat4 (f32) and Mat4d (f64) 4x4 transformation matrices with column-major storage.

## Key Concepts
| Concept | Description |
|---------|-------------|
| Column-major | GPU/Vulkan standard storage order |
| Transform | Translation, rotation, scale factories |
| Projection | Perspective and orthographic projection |

## Behavior
- Column-major storage for GPU compatibility
- Factory methods for common transforms
- Matrix multiplication and inverse
- Point and vector transformation

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/mat4/result.json` |

## Scenarios

- creates identity matrix
- creates translation matrix
- creates scale matrix
- multiplies identity by identity
- multiplies translation matrices
- transforms a point
- transforms a direction vector (ignores translation)
- extracts 3x3 submatrix
- inverts identity to identity
- inverts translation
