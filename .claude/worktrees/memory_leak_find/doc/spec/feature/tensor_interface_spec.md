# Tensor Interface Consistency Specification

**Feature ID:** #1920, #1930 | **Category:** ML, Collections, API | **Status:** Complete

_Source: `test/feature/usage/tensor_interface_spec.spl`_

---

Tests that tensor interfaces are consistent between core and torch.
Verifies that basic tensor operations work the same way regardless
of the underlying implementation.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 21 |

## Test Structure

### Tensor Interface Consistency

#### tensor creation

- ✅ creates tensor from array
- ✅ creates tensor with explicit shape
- ✅ creates zero tensor
- ✅ creates ones tensor
#### tensor indexing

- ✅ accesses elements by index
- ✅ supports negative indexing
- ✅ slices tensors
#### tensor operations

- ✅ performs element-wise addition
- ✅ performs element-wise multiplication
- ✅ performs matrix multiplication with @
#### tensor properties

- ✅ gets tensor shape
- ✅ gets tensor dimension count
- ✅ gets tensor element count
- ✅ gets tensor dtype
- ✅ gets tensor device
#### tensor reshaping

- ✅ reshapes tensor
- ✅ flattens tensor
- ✅ transposes 2D tensor
#### tensor with dict config

- ✅ creates tensor with device config
- ✅ creates tensor metadata dict
- ✅ stores tensor info in dict

