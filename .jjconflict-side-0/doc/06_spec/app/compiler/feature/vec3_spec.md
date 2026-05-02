# Vec3 Specification

**Feature ID:** #MATH-001 | **Category:** Stdlib | **Difficulty:** 2/5 | **Status:** Implemented

_Source: `test/feature/usage/vec3_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 23 |

## Test Structure

### Vec3 Construction

- ✅ creates a vector with components
- ✅ creates zero vector
- ✅ creates one vector
- ✅ creates directional vectors
### Vec3 Arithmetic

- ✅ adds two vectors
- ✅ subtracts two vectors
- ✅ scales a vector
- ✅ computes dot product
- ✅ computes cross product
### Vec3 Geometric Methods

- ✅ computes magnitude
- ✅ magnitude and length are aliases
- ✅ normalizes a vector
- ✅ computes distance
- ✅ distance and distance_to are aliases
- ✅ interpolates linearly
### Vec3 Utility Methods

- ✅ detects zero vector
- ✅ detects near-zero vector
- ✅ checks unit vector
- ✅ computes component min/max
### Vec3d and Conversions

- ✅ creates Vec3d with f64 precision
- ✅ converts Vec3 to Vec3d
- ✅ converts Vec3d to Vec3
- ✅ Vec3d has all Vec3 methods

