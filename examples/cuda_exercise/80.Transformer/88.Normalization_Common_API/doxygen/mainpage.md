# Module 88: Normalization_Common_API

## Overview

This module provides reusable warp-level and block-level reduction primitives, along with mean/variance/RMS computation helpers used by normalization layers (LayerNorm, RMSNorm) in transformer inference kernels.

## Module Architecture

The module is organized into the following components:

- **common/**: Core reduction and normalization primitives
  - `reduce_warp.cuh` - Warp-level reductions (sum, max, min) via `__shfl_xor_sync`
  - `reduce_block.cuh` - Block-level reductions using shared memory + warp primitives
  - `mean_rsqrt.cuh` - Mean, variance, and RMS reciprocal square root helpers

## Key Components

### Warp-Level Reductions (`reduce_warp.cuh`)

Butterfly shuffle-based reductions that operate within a single warp (32 threads):

- `warp_reduce_sum(float val)` - Sum reduction across all 32 lanes
- `warp_reduce_max(float val)` - Max reduction across all 32 lanes
- `warp_reduce_min(float val)` - Min reduction across all 32 lanes
- `warp_reduce_sum_partial(float val, int active_lanes)` - Partial warp sum with custom mask

### Block-Level Reductions (`reduce_block.cuh`)

Two-phase reductions that work across an entire thread block:

1. Intra-warp reduction via shuffle
2. Inter-warp reduction via shared memory

- `block_reduce_sum(float val, float* smem)` - Block-wide sum
- `block_reduce_max(float val, float* smem)` - Block-wide max

### Normalization Helpers (`mean_rsqrt.cuh`)

Higher-level functions that combine strided data access with block reductions:

- `compute_mean(input, n, smem)` - Row mean for LayerNorm
- `compute_variance(input, mean, n, smem)` - Row variance for LayerNorm
- `compute_rms_rsqrt(input, n, eps, smem)` - `rsqrt(mean(x^2) + eps)` for RMSNorm

## Usage Examples

See the `test/` directory for comprehensive usage examples:

- `test/unit/kernels/test_reduce_warp.cu` - Warp reduction tests
- `test/unit/kernels/test_reduce_block.cu` - Block reduction tests with various thread counts
- `test/unit/kernels/test_mean_rsqrt.cu` - Mean, variance, and RMS tests against CPU references

## Building Documentation

From the build directory:
```bash
ninja doxygen_88_Normalization_Common_API
```

The generated HTML documentation will be available at:
```
build/80.Transformer/88.Normalization_Common_API/doxygen/html/index.html
```

## Dependencies

- CUDA Runtime (`cuda_runtime.h`)
- CudaCustomLib (shared CUDA utilities)

## See Also

- Module README.md for detailed learning materials
- Test files for usage examples
- Related modules: 84.Normalization (uses these primitives)
