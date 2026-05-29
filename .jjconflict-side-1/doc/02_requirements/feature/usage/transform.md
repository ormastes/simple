# Transform Specification
*Source:* `test/feature/usage/transform_spec.spl`
**Feature IDs:** #MATH-004  |  **Category:** Stdlib  |  **Status:** Implemented

## Overview



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

## Feature: Transform Construction

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates identity transform | pass |
| 2 | converts to mat4 | pass |

**Example:** creates identity transform
    Given val t = math.Transform.identity()
    Then  expect t.position.is_zero() == true
    Then  expect t.rotation.w == 1.0
    Then  expect t.scale.x == 1.0
    Then  expect t.scale.y == 1.0
    Then  expect t.scale.z == 1.0

**Example:** converts to mat4
    Given val t = math.Transform.identity()
    Given val m = t.to_mat4()
    Then  expect m.data[0] == 1.0
    Then  expect m.data[5] == 1.0
    Then  expect m.data[10] == 1.0
    Then  expect m.data[15] == 1.0

## Feature: Transform Direction Vectors

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | identity forward is +Z | pass |
| 2 | identity right is +X | pass |
| 3 | identity up is +Y | pass |

**Example:** identity forward is +Z
    Given val t = math.Transform.identity()
    Given val fwd = t.forward()
    Then  expect fwd.z == 1.0

**Example:** identity right is +X
    Given val t = math.Transform.identity()
    Given val r = t.right()
    Then  expect r.x == 1.0

**Example:** identity up is +Y
    Given val t = math.Transform.identity()
    Given val u = t.up()
    Then  expect u.y == 1.0

## Feature: Transform Composition

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | combines identity transforms | pass |
| 2 | combines translation | pass |
| 3 | transforms a point | pass |

**Example:** combines identity transforms
    Given val parent = math.Transform.identity()
    Given val child = math.Transform.identity()
    Given val combined = parent.combine(child)
    Then  expect combined.position.is_zero() == true

**Example:** combines translation
    Given val parent = math.Transform(
    Given val child = math.Transform(
    Given val combined = parent.combine(child)
    Then  expect combined.position.x == 15.0

**Example:** transforms a point
    Given val t = math.Transform(
    Given val p = math.Vec3(1.0, 2.0, 3.0)
    Given val result = t.transform_point(p)
    Then  expect result.x == 11.0
    Then  expect result.y == 22.0
    Then  expect result.z == 33.0

## Feature: Transform Interpolation

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | lerps between transforms | pass |

**Example:** lerps between transforms
    Given val a = math.Transform(
    Given val b = math.Transform(
    Given val mid = a.lerp(b, 0.5)
    Then  expect mid.position.x == 5.0
    Then  expect mid.position.y == 5.0
    Then  expect mid.position.z == 5.0


