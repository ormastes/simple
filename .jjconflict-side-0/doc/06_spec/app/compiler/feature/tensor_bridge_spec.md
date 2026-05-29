# Tensor Bridge Batch Conversion

**Feature ID:** #ML-001 | **Category:** Runtime | **Status:** Active

_Source: `test/feature/usage/tensor_bridge_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 5 |

## Test Structure

### Tensor Bridge Batch Conversion

- ✅ arrtens Vec3 list to array
- ✅ unarrtens array to Vec3 list
- ✅ round-trips Vec3 list
### Tensor Bridge Vec3d Batch Conversion

- ✅ arrtens Vec3d list to f64 array
- ✅ unarrtens f64 array to Vec3d list

