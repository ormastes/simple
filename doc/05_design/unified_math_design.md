# Unified Math Module Design

**Created:** 2026-02-01
**Status:** Implemented
**Location:** `rust/lib/std/src/math/`

## Overview

The `math` module provides shared mathematical types used by physics, game engine, graphics, and ML subsystems. It replaces the inline types previously defined in `physics/core/__init__.spl`.

## Type Hierarchy

| File | f32 Type | f64 Type | Key Methods |
|------|----------|----------|-------------|
| `vec2.spl` | `Vec2` | `Vec2d` | add, sub, scale, dot, magnitude/length, normalize, distance, lerp |
| `vec3.spl` | `Vec3` | `Vec3d` | Same + cross, length_squared, component_min/max, is_unit, has_nan |
| `vec4.spl` | `Vec4` | `Vec4d` | add, sub, scale, dot, magnitude/length, normalize, lerp |
| `mat3.spl` | `Mat3` | `Mat3d` | identity, rotation_z, scale, mul, transpose, determinant |
| `mat4.spl` | `Mat4` | `Mat4d` | identity, translation, rotation_x/y/z, scale, perspective, ortho, look_at, inverse, mul, transpose, transform_point/vec3 |
| `quat.spl` | `Quat` | `Quatd` | identity, from_axis_angle, from_euler, slerp, normalize, conjugate, inverse, mul, rotate_vector, to_mat3/mat4 |
| `transform.spl` | `Transform` | `Transformd` | identity, to_mat4, forward/right/up, inverse, lerp, combine, transform_point/vector |
| `color.spl` | `Color` | `Color32` (u8) | red/green/blue/white/black, lerp, to_hex, from_hex |

## Precision Strategy

- **f32 types** (`Vec3`, `Mat4`, `Quat`, `Transform`): GPU rendering, real-time physics
- **f64 types** (`Vec3d`, `Mat4d`, `Quatd`, `Transformd`): Physics simulation, scientific computing
- Conversion methods: `to_f64()` / `to_f32()` on all vector/quat types

## Naming Conventions

### Aliases (Backward Compatibility)

| Alias | Target | Used By |
|-------|--------|---------|
| `Vector2` | `Vec2d` | physics module |
| `Vector3` | `Vec3d` | physics module |
| `Matrix3` | `Mat3d` | physics module |
| `Matrix4` | `Mat4d` | physics module |
| `Quaternion` | `Quatd` | physics module |

### Method Aliases

| Primary | Alias | Context |
|---------|-------|---------|
| `magnitude()` | `length()` | Graphics uses "length" |
| `distance()` | `distance_to()` | Game engines use "distance_to" |
| `scale()` | operator `*` | Named method for pipeline readability |

## Matrix Storage

**Column-major** everywhere (GPU/Vulkan standard).

```
# Column-major layout for Mat4:
# Column 0: data[0..3]   = (m00, m10, m20, m30)
# Column 1: data[4..7]   = (m01, m11, m21, m31)
# Column 2: data[8..11]  = (m02, m12, m22, m32)
# Column 3: data[12..15] = (m03, m13, m23, m33)
```

**Migration from physics:** The original physics matrices were row-major. The `physics/core/__init__.spl` now re-exports math types (column-major). Existing physics code using `core.Vector3` etc. continues to work via type aliases.

## Tensor Bridge

`tensor_bridge.spl` provides conversion between math types and PyTorch tensors:
- `Vec3.to_tensor(device)` → `[3]` tensor
- `Mat4.to_tensor(device)` → `[4,4]` tensor
- `vecs_to_tensor([Vec3], device)` → `[N,3]` tensor
- Batch conversion functions implemented and tested: `vecs_to_tensor()`, `tensor_to_vecs()`, `vecs3d_to_tensor()`, `tensor_to_vecs3d()`

## Module Consumers

| Module | Types Used | Precision |
|--------|-----------|-----------|
| `physics/core` | `Vec2d`, `Vec3d`, `Mat3d`, `Mat4d`, `Quatd` (via aliases) | f64 |
| `physics/gpu_batch` | `Vec3d` (via core.Vector3) | f64 |
| `game_engine/actor_model` | `Vec3` | f32 |
| `game_engine/scene_node` | `Vec3d`, `Quatd`, `Transformd` | f64 |
| `game_engine/physics` | `Vec3` | f32 |
| `game_engine/component` | `Vec3` | f32 |
