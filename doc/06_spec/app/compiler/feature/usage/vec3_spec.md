# Vec3 Specification

Vec3 (f32) and Vec3d (f64) 3D vector types with arithmetic, geometric, and utility methods.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MATH-001 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/feature/usage/vec3_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview
Vec3 (f32) and Vec3d (f64) 3D vector types with arithmetic, geometric, and utility methods.

## Key Concepts
| Concept | Description |
|---------|-------------|
| Vec3 | 3D vector with f32 precision |
| Vec3d | 3D vector with f64 precision |
| Dual precision | All types in both f32 and f64 |

## Behavior
- Supports add, sub, scale, dot, cross operations
- Magnitude/length aliases
- Static factory methods for common directions
- Conversion between f32 and f64

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/vec3/result.json` |

## Scenarios

- creates a vector with components
- creates zero vector
- creates one vector
- creates directional vectors
- adds two vectors
- subtracts two vectors
- scales a vector
- computes dot product
- computes cross product
- computes magnitude
- magnitude and length are aliases
- normalizes a vector
- computes distance
- distance and distance_to are aliases
- interpolates linearly
- detects zero vector
- detects near-zero vector
- checks unit vector
- computes component min/max
- creates Vec3d with f64 precision
- converts Vec3 to Vec3d
- converts Vec3d to Vec3
- Vec3d has all Vec3 methods
