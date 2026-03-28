# Quaternion Specification
*Source:* `test/feature/usage/quat_spec.spl`
**Feature IDs:** #MATH-003  |  **Category:** Stdlib  |  **Status:** Implemented

## Overview




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

## Feature: Quaternion Construction

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates identity quaternion | pass |
| 2 | creates from axis-angle | pass |
| 3 | normalizes a quaternion | pass |

**Example:** creates identity quaternion
    Given val q = math.Quat.identity()
    Then  expect q.w == 1.0
    Then  expect q.x == 0.0
    Then  expect q.y == 0.0
    Then  expect q.z == 0.0

**Example:** creates from axis-angle
    Given val axis = math.Vec3(0.0, 1.0, 0.0)
    Given val q = math.Quat.from_axis_angle(axis, 0.0)
    Then  expect q.w == 1.0

**Example:** normalizes a quaternion
    Given val q = math.Quat(2.0, 0.0, 0.0, 0.0)
    Given val n = q.normalize()
    Then  expect n.w == 1.0
    Then  expect n.x == 0.0

## Feature: Quaternion Rotation

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | identity rotation leaves vector unchanged | pass |
| 2 | composes rotations via multiplication | pass |
| 3 | conjugate negates vector part | pass |

**Example:** identity rotation leaves vector unchanged
    Given val q = math.Quat.identity()
    Given val v = math.Vec3(1.0, 2.0, 3.0)
    Given val r = q.rotate_vector(v)
    Then  expect r.x == 1.0
    Then  expect r.y == 2.0
    Then  expect r.z == 3.0

**Example:** composes rotations via multiplication
    Given val q1 = math.Quat.identity()
    Given val q2 = math.Quat.identity()
    Given val q3 = q1.mul(q2)
    Then  expect q3.w == 1.0
    Then  expect q3.x == 0.0

**Example:** conjugate negates vector part
    Given val q = math.Quat(1.0, 2.0, 3.0, 4.0)
    Given val c = q.conjugate()
    Then  expect c.w == 1.0
    Then  expect c.x == -2.0
    Then  expect c.y == -3.0
    Then  expect c.z == -4.0

## Feature: Quaternion SLERP

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | slerp at t=0 returns start | pass |
| 2 | slerp at t=1 returns end | pass |

**Example:** slerp at t=0 returns start
    Given val a = math.Quat.identity()
    Given val b = math.Quat.from_axis_angle(math.Vec3.up(), 1.57)
    Given val r = a.slerp(b, 0.0)
    Then  expect r.w == a.w

**Example:** slerp at t=1 returns end
    Given val a = math.Quat.identity()
    Given val axis = math.Vec3(0.0, 1.0, 0.0)
    Given val b = math.Quat.from_axis_angle(axis, 1.57)
    Given val r = a.slerp(b, 1.0)
    Given val diff = (r.w - b.w).abs()
    Then  expect diff < 0.01

## Feature: Quaternion Conversions

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | converts to rotation matrix | pass |
| 2 | converts between f32 and f64 | pass |

**Example:** converts to rotation matrix
    Given val q = math.Quat.identity()
    Given val m = q.to_mat4()
    Then  expect m.data[0] == 1.0
    Then  expect m.data[5] == 1.0
    Then  expect m.data[10] == 1.0

**Example:** converts between f32 and f64
    Given val q32 = math.Quat(1.0, 0.0, 0.0, 0.0)
    Given val q64 = q32.to_f64()
    Then  expect q64.w == 1.0
    Given val q32b = q64.to_f32()
    Then  expect q32b.w == 1.0


