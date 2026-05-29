# Mat4 Specification
*Source:* `test/feature/usage/mat4_spec.spl`
**Feature IDs:** #MATH-002  |  **Category:** Stdlib  |  **Status:** Implemented

## Overview



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

## Feature: Mat4 Identity and Factories

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates identity matrix | pass |
| 2 | creates translation matrix | pass |
| 3 | creates scale matrix | pass |

**Example:** creates identity matrix
    Given val m = math.Mat4.identity()
    Then  expect m.data[0] == 1.0
    Then  expect m.data[5] == 1.0
    Then  expect m.data[10] == 1.0
    Then  expect m.data[15] == 1.0
    Then  expect m.data[1] == 0.0

**Example:** creates translation matrix
    Given val m = math.Mat4.translation(1.0, 2.0, 3.0)
    Then  expect m.data[12] == 1.0
    Then  expect m.data[13] == 2.0
    Then  expect m.data[14] == 3.0

**Example:** creates scale matrix
    Given val m = math.Mat4.scale(2.0, 3.0, 4.0)
    Then  expect m.data[0] == 2.0
    Then  expect m.data[5] == 3.0
    Then  expect m.data[10] == 4.0

## Feature: Mat4 Operations

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | multiplies identity by identity | pass |
| 2 | multiplies translation matrices | pass |
| 3 | transforms a point | pass |
| 4 | transforms a direction vector (ignores translation) | pass |
| 5 | extracts 3x3 submatrix | pass |

**Example:** multiplies identity by identity
    Given val a = math.Mat4.identity()
    Given val b = math.Mat4.identity()
    Given val c = a.mul(b)
    Then  expect c.data[0] == 1.0
    Then  expect c.data[5] == 1.0
    Then  expect c.data[10] == 1.0
    Then  expect c.data[15] == 1.0

**Example:** multiplies translation matrices
    Given val a = math.Mat4.translation(1.0, 0.0, 0.0)
    Given val b = math.Mat4.translation(0.0, 2.0, 0.0)
    Given val c = a.mul(b)
    Then  expect c.data[12] == 1.0
    Then  expect c.data[13] == 2.0
    Then  expect c.data[14] == 0.0

**Example:** transforms a point
    Given val m = math.Mat4.translation(10.0, 20.0, 30.0)
    Given val p = math.Vec3(1.0, 2.0, 3.0)
    Given val result = m.transform_point(p)
    Then  expect result.x == 11.0
    Then  expect result.y == 22.0
    Then  expect result.z == 33.0

**Example:** transforms a direction vector (ignores translation)
    Given val m = math.Mat4.translation(10.0, 20.0, 30.0)
    Given val v = math.Vec3(1.0, 0.0, 0.0)
    Given val result = m.transform_vec3(v)
    Then  expect result.x == 1.0
    Then  expect result.y == 0.0
    Then  expect result.z == 0.0

**Example:** extracts 3x3 submatrix
    Given val m = math.Mat4.scale(2.0, 3.0, 4.0)
    Given val m3 = m.to_mat3()
    Then  expect m3.data[0] == 2.0
    Then  expect m3.data[4] == 3.0
    Then  expect m3.data[8] == 4.0

## Feature: Mat4 Inverse

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | inverts identity to identity | pass |
| 2 | inverts translation | pass |

**Example:** inverts identity to identity
    Given val m = math.Mat4.identity()
    Given val inv = m.inverse()
    Then  expect inv.data[0] == 1.0
    Then  expect inv.data[5] == 1.0

**Example:** inverts translation
    Given val m = math.Mat4.translation(5.0, 10.0, 15.0)
    Given val inv = m.inverse()
    Then  expect inv.data[12] == -5.0
    Then  expect inv.data[13] == -10.0
    Then  expect inv.data[14] == -15.0


