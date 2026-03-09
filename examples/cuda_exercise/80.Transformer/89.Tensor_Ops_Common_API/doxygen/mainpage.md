# Module 89: Tensor Ops Common API

## Overview

This module provides vectorized I/O and memory layout utilities that form the foundation
for all transformer kernel modules. These primitives are used throughout the 80.Transformer
suite to achieve high memory bandwidth utilization and correct Tensor Core data layouts.

## Module Architecture

The module is organized into the following components:

- **common/vector_io.cuh**: Vectorized load/store templates (float4, float2, half2)
  - Type-safe wrappers around reinterpret_cast-based vectorized memory access
  - Alignment checking utilities for safe vectorized operations
  - Generic vectorized_copy with automatic fallback for unaligned addresses

- **common/layout_swizzle.cuh**: Memory layout index calculators
  - Row-major, column-major, and Col32 (Tensor Core) layout support
  - StrideHelper for generic 3D tensor indexing
  - Shared memory swizzle function for bank conflict avoidance

## Key Components

### Vectorized I/O (`vector_io.cuh`)

- `load_float4()` / `store_float4()` - 128-bit vectorized float access
- `load_float2()` / `store_float2()` - 64-bit vectorized float access
- `load_half2()` / `store_half2()` - 32-bit vectorized half-precision access
- `is_aligned<N>()` - Compile-time alignment check template
- `safe_load_float4()` - Alignment-aware load with scalar fallback
- `vectorized_copy<VEC_SIZE>()` - Bulk copy with automatic vectorization

### Layout Utilities (`layout_swizzle.cuh`)

- `row_major_idx()` / `col_major_idx()` - Standard layout index computation
- `col32_padded()` / `col32_idx()` - Tensor Core Col32 layout support
- `StrideHelper` / `make_row_major_3d()` - Generic 3D stride computation
- `smem_swizzle()` - XOR-based shared memory bank conflict avoidance

## Usage Examples

See the `test/` directory for comprehensive usage examples:

- `test/unit/kernels/test_vector_io.cu` - Vectorized I/O roundtrip and copy tests
- `test/unit/kernels/test_layout_swizzle.cu` - Layout indexing and swizzle tests

## Building Documentation

From the build directory:
```bash
ninja doxygen_89_Tensor_Ops_Common_API
```

The generated HTML documentation will be available at:
```
build/80.Transformer/89.Tensor_Ops_Common_API/doxygen/html/index.html
```

## Dependencies

- CUDA Runtime (`cuda_runtime.h`)
- CUDA FP16 (`cuda_fp16.h`)
- CudaCustomLib (project common utilities)

## Performance Considerations

- Vectorized loads (float4) achieve 4x the bandwidth of scalar loads when data is 16-byte aligned
- Col32 layout eliminates bank conflicts for Tensor Core WMMA fragment loads
- The smem_swizzle function uses a lightweight XOR operation with no branch overhead

## See Also

- Module README.md for detailed learning materials
- 86.Core_Common_API for GEMM kernels that consume these utilities
- 82.Attention_Kernels for attention kernels using vectorized I/O
- 85.Tensor_Operations for transpose/permute using layout helpers
