# Quaternion Specification

Quat (f32) and Quatd (f64) quaternion types for 3D rotations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MATH-003 |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/feature/usage/quat_spec.spl` |
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
Quat (f32) and Quatd (f64) quaternion types for 3D rotations.

## Key Concepts
| Concept | Description |
|---------|-------------|
| Quat | Quaternion with f32 precision |
| SLERP | Spherical linear interpolation |
| Composition | Rotation composition via multiplication |

## Behavior
- Identity quaternion represents no rotation
- from_axis_angle and from_euler constructors
- SLERP interpolation for smooth rotation
- Quaternion-vector rotation

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/quat/result.json` |

## Scenarios

- creates identity quaternion
- creates from axis-angle
- normalizes a quaternion
- identity rotation leaves vector unchanged
- composes rotations via multiplication
- conjugate negates vector part
- slerp at t=0 returns start
- slerp at t=1 returns end
- converts to rotation matrix
- converts between f32 and f64
