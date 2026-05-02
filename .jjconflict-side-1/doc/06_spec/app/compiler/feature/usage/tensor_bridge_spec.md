# Tensor Bridge Batch Conversion

Tests batch conversion between math vector types (Vec3, Vec3d) and flat tensor arrays. Validates flattening Vec3 lists to float arrays, unflattening arrays back to Vec3 lists, round-trip consistency, and equivalent operations for double-precision Vec3d types.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ML-001 |
| Category | Runtime |
| Status | Active |
| Source | `test/feature/usage/tensor_bridge_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests batch conversion between math vector types (Vec3, Vec3d) and flat tensor
arrays. Validates flattening Vec3 lists to float arrays, unflattening arrays
back to Vec3 lists, round-trip consistency, and equivalent operations for
double-precision Vec3d types.

## Syntax

```simple
val vecs = [math.Vec3(1.0, 2.0, 3.0), math.Vec3(4.0, 5.0, 6.0)]
val arr = math.vecs_to_tensor(vecs)
val restored = math.tensor_to_vecs(arr)
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/tensor_bridge/result.json` |

## Scenarios

- arrtens Vec3 list to array
- unarrtens array to Vec3 list
- round-trips Vec3 list
- arrtens Vec3d list to f64 array
- unarrtens f64 array to Vec3d list
