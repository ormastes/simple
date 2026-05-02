# Mat4 Specification

**Feature ID:** #MATH-002 | **Category:** Stdlib | **Difficulty:** 3/5 | **Status:** Implemented

_Source: `test/feature/usage/mat4_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 10 |

## Test Structure

### Mat4 Identity and Factories

- ✅ creates identity matrix
- ✅ creates translation matrix
- ✅ creates scale matrix
### Mat4 Operations

- ✅ multiplies identity by identity
- ✅ multiplies translation matrices
- ✅ transforms a point
- ✅ transforms a direction vector (ignores translation)
- ✅ extracts 3x3 submatrix
### Mat4 Inverse

- ✅ inverts identity to identity
- ✅ inverts translation

