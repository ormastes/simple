# Module 83: MLP

## Overview

This module provides standalone GPU activation function kernels (GELU, SiLU, SwiGLU) used in transformer feed-forward network (MLP) layers. These kernels handle cases where the activation cannot be fused into a GEMM epilogue, such as gated projections in LLaMA-style architectures.

## Module Architecture

The module is organized into the following components:

- **common/**: Public API headers
  - `activation.cuh` - Launch function declarations for all activation variants

- **kernels/**: CUDA kernel implementations
  - `activation.cu` - GELU, SiLU, SwiGLU kernels in fp32 and fp16

## Key Components

### Activation Functions

- `launch_gelu(output, input, n, stream)` - Gaussian Error Linear Unit (tanh approximation)
- `launch_silu(output, input, n, stream)` - Sigmoid Linear Unit (Swish)
- `launch_swiglu(output, input, n, stream)` - Gated SiLU for LLaMA FFN
- `launch_gelu_fp16(output, input, n, stream)` - Half-precision GELU

## Usage Examples

See `test/unit/kernels/test_activation.cu` for tests covering:
- GELU correctness against CPU reference
- SiLU correctness against CPU reference
- SwiGLU with split input (x, gate) and zero-gate edge case
- fp16 GELU with appropriate tolerance

## Building Documentation

From the build directory:
```bash
ninja doxygen_83_MLP
```

## Dependencies

- 81_Core_GEMM_Operations (for linear layer wrappers used in full MLP blocks)
- CudaCustomLib, CUDA Runtime

## See Also

- [81.Core_GEMM_Operations](../81.Core_GEMM_Operations/README.md) - GEMM dispatcher and epilogue fusion
- [86.Core_Common_API](../86.Core_Common_API/README.md) - Fused GELU in GEMM epilogue
