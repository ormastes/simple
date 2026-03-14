# Vec3 Specification
*Source:* `test/feature/usage/vec3_spec.spl`
**Feature IDs:** #MATH-001  |  **Category:** Stdlib  |  **Status:** Implemented

## Overview




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

## Feature: Vec3 Construction

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates a vector with components | pass |
| 2 | creates zero vector | pass |
| 3 | creates one vector | pass |
| 4 | creates directional vectors | pass |

**Example:** creates a vector with components
    Given val v = math.Vec3(1.0, 2.0, 3.0)
    Then  expect v.x == 1.0
    Then  expect v.y == 2.0
    Then  expect v.z == 3.0

**Example:** creates zero vector
    Given val v = math.Vec3.zero()
    Then  expect v.x == 0.0
    Then  expect v.y == 0.0
    Then  expect v.z == 0.0

**Example:** creates one vector
    Given val v = math.Vec3.one()
    Then  expect v.x == 1.0
    Then  expect v.y == 1.0
    Then  expect v.z == 1.0

**Example:** creates directional vectors
    Then  expect math.Vec3.up().y == 1.0
    Then  expect math.Vec3.down().y == -1.0
    Then  expect math.Vec3.left().x == -1.0
    Then  expect math.Vec3.right().x == 1.0
    Then  expect math.Vec3.forward().z == 1.0
    Then  expect math.Vec3.back().z == -1.0

## Feature: Vec3 Arithmetic

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | adds two vectors | pass |
| 2 | subtracts two vectors | pass |
| 3 | scales a vector | pass |
| 4 | computes dot product | pass |
| 5 | computes cross product | pass |

**Example:** adds two vectors
    Given val a = math.Vec3(1.0, 2.0, 3.0)
    Given val b = math.Vec3(4.0, 5.0, 6.0)
    Given val c = a.add(b)
    Then  expect c.x == 5.0
    Then  expect c.y == 7.0
    Then  expect c.z == 9.0

**Example:** subtracts two vectors
    Given val a = math.Vec3(4.0, 5.0, 6.0)
    Given val b = math.Vec3(1.0, 2.0, 3.0)
    Given val c = a.sub(b)
    Then  expect c.x == 3.0
    Then  expect c.y == 3.0
    Then  expect c.z == 3.0

**Example:** scales a vector
    Given val v = math.Vec3(1.0, 2.0, 3.0)
    Given val s = v.scale(2.0)
    Then  expect s.x == 2.0
    Then  expect s.y == 4.0
    Then  expect s.z == 6.0

**Example:** computes dot product
    Given val a = math.Vec3(1.0, 0.0, 0.0)
    Given val b = math.Vec3(0.0, 1.0, 0.0)
    Then  expect a.dot(b) == 0.0
    Given val c = math.Vec3(1.0, 2.0, 3.0)
    Given val d = math.Vec3(4.0, 5.0, 6.0)
    Then  expect c.dot(d) == 32.0

**Example:** computes cross product
    Given val x = math.Vec3(1.0, 0.0, 0.0)
    Given val y = math.Vec3(0.0, 1.0, 0.0)
    Given val z = x.cross(y)
    Then  expect z.x == 0.0
    Then  expect z.y == 0.0
    Then  expect z.z == 1.0

## Feature: Vec3 Geometric Methods

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | computes magnitude | pass |
| 2 | magnitude and length are aliases | pass |
| 3 | normalizes a vector | pass |
| 4 | computes distance | pass |
| 5 | distance and distance_to are aliases | pass |
| 6 | interpolates linearly | pass |

**Example:** computes magnitude
    Given val v = math.Vec3(3.0, 4.0, 0.0)
    Then  expect v.magnitude() == 5.0

**Example:** magnitude and length are aliases
    Given val v = math.Vec3(3.0, 4.0, 0.0)
    Then  expect v.magnitude() == v.length()

**Example:** normalizes a vector
    Given val v = math.Vec3(3.0, 0.0, 0.0)
    Given val n = v.normalize()
    Then  expect n.x == 1.0
    Then  expect n.y == 0.0
    Then  expect n.z == 0.0

**Example:** computes distance
    Given val a = math.Vec3(0.0, 0.0, 0.0)
    Given val b = math.Vec3(3.0, 4.0, 0.0)
    Then  expect a.distance(b) == 5.0

**Example:** distance and distance_to are aliases
    Given val a = math.Vec3(0.0, 0.0, 0.0)
    Given val b = math.Vec3(3.0, 4.0, 0.0)
    Then  expect a.distance(b) == a.distance_to(b)

**Example:** interpolates linearly
    Given val a = math.Vec3(0.0, 0.0, 0.0)
    Given val b = math.Vec3(10.0, 10.0, 10.0)
    Given val mid = a.lerp(b, 0.5)
    Then  expect mid.x == 5.0
    Then  expect mid.y == 5.0
    Then  expect mid.z == 5.0

## Feature: Vec3 Utility Methods

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | detects zero vector | pass |
| 2 | detects near-zero vector | pass |
| 3 | checks unit vector | pass |
| 4 | computes component min/max | pass |

**Example:** detects zero vector
    Then  expect math.Vec3.zero().is_zero() == true
    Then  expect math.Vec3(1.0, 0.0, 0.0).is_zero() == false

**Example:** detects near-zero vector
    Given val v = math.Vec3(0.0000001, 0.0, 0.0)
    Then  expect v.is_near_zero() == true

**Example:** checks unit vector
    Then  expect math.Vec3(1.0, 0.0, 0.0).is_unit() == true
    Then  expect math.Vec3(2.0, 0.0, 0.0).is_unit() == false

**Example:** computes component min/max
    Given val a = math.Vec3(1.0, 5.0, 3.0)
    Given val b = math.Vec3(4.0, 2.0, 6.0)
    Given val mn = a.component_min(b)
    Given val mx = a.component_max(b)
    Then  expect mn.x == 1.0
    Then  expect mn.y == 2.0
    Then  expect mn.z == 3.0
    Then  expect mx.x == 4.0
    Then  expect mx.y == 5.0
    Then  expect mx.z == 6.0

## Feature: Vec3d and Conversions

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates Vec3d with f64 precision | pass |
| 2 | converts Vec3 to Vec3d | pass |
| 3 | converts Vec3d to Vec3 | pass |
| 4 | Vec3d has all Vec3 methods | pass |

**Example:** creates Vec3d with f64 precision
    Given val v = math.Vec3d(1.0, 2.0, 3.0)
    Then  expect v.x == 1.0
    Then  expect v.y == 2.0
    Then  expect v.z == 3.0

**Example:** converts Vec3 to Vec3d
    Given val v32 = math.Vec3(1.0, 2.0, 3.0)
    Given val v64 = v32.to_f64()
    Then  expect v64.x == 1.0
    Then  expect v64.y == 2.0
    Then  expect v64.z == 3.0

**Example:** converts Vec3d to Vec3
    Given val v64 = math.Vec3d(1.0, 2.0, 3.0)
    Given val v32 = v64.to_f32()
    Then  expect v32.x == 1.0
    Then  expect v32.y == 2.0
    Then  expect v32.z == 3.0

**Example:** Vec3d has all Vec3 methods
    Given val a = math.Vec3d(1.0, 2.0, 3.0)
    Given val b = math.Vec3d(4.0, 5.0, 6.0)
    Then  expect a.dot(b) == 32.0
    Given val c = a.cross(b)
    Then  expect c.x == -3.0
    Then  expect c.y == 6.0
    Then  expect c.z == -3.0


