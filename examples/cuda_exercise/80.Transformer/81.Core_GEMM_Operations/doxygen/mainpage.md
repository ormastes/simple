# Module 81: Core_GEMM_Operations

## Overview

This module provides a high-level GEMM dispatcher that automatically selects the best backend kernel (Tensor Core WMMA for fp16, shared-memory SIMT for fp32) and exposes epilogue fusion helpers for common transformer linear-layer patterns.

## Module Architecture

The module is organized into the following components:

- **common/**: Public API headers
  - `gemm_ops.cuh` - Unified GEMM dispatcher (GemmParams, gemm, gemm_with_bias_act)
  - `epilogue_fusion.cuh` - Convenience wrappers (linear, linear_gelu)

- **kernels/**: Dispatcher implementation
  - `gemm_ops.cu` - Routes calls to 86_Core_Common_API backends

## Key Components

### GEMM Dispatcher (`gemm_ops.cuh`)

- `GemmParams` - Configuration struct with fp32/fp16 pointers, dimensions, and backend preference
- `gemm(const GemmParams&)` - Auto-selecting dispatch entry point
- `gemm_with_bias_act(...)` - GEMM with fused bias + optional GELU activation

### Epilogue Fusion (`epilogue_fusion.cuh`)

- `linear(...)` - Standard dense layer (matmul + bias)
- `linear_gelu(...)` - Fused dense + GELU activation

## Usage Examples

See `test/unit/kernels/test_gemm_ops.cu` for correctness tests covering:
- Small (16x16), medium (128x128), and non-square (64x128x96) GEMM
- GEMM with bias addition
- GEMM with fused GELU activation
- Convenience wrapper (linear) validation

## Building Documentation

From the build directory:
```bash
ninja doxygen_81_Core_GEMM_Operations
```

## Dependencies

- 86_Core_Common_API (SIMT and WMMA GEMM backends, epilogue infrastructure)
- CudaCustomLib, CUDA Runtime

## See Also

- [86.Core_Common_API](../86.Core_Common_API/README.md) - Backend GEMM implementations
- [83.MLP](../83.MLP/README.md) - Uses linear/linear_gelu for FFN layers
