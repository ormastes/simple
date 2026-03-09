# Module 86: Core_Common_API

## Overview

This module provides hand-rolled GEMM (General Matrix Multiply) backends for transformer inference, including SIMT shared-memory tiling, Tensor Core WMMA, and INT8 DP4A implementations with fused epilogue operations.

## Module Architecture

The module is organized into the following components:

- **common/**: Shared epilogue fusion and autotuning interfaces
  - `epilogue_kernels.cuh` - Fused bias, activation (GELU/SiLU/ReLU), and residual store
  - `autotune_registry.cuh` - Shape-to-kernel cache for runtime kernel selection

- **kernels/**: CUDA kernel implementations
  - `gemm_simt.cu` - Shared-memory tiled SIMT GEMM (fp32)
  - `gemm_wmma_tc.cu` - Tensor Core WMMA GEMM (fp16 inputs, fp32 accumulation)
  - `gemm_int8_dp4a.cu` - INT8 DP4A GEMM for quantized inference
  - `autotune_registry.cu` - Runtime autotuning cache implementation

## Key Components

### Epilogue Fusion

The `Epilogue` struct configures fused post-GEMM operations:
- Bias addition
- Activation functions (GELU, SiLU, ReLU)
- Output scaling
- Residual connections

### GEMM Backends

| Backend | Precision | Hardware | Use Case |
|---------|-----------|----------|----------|
| SIMT | FP32 | All GPUs | General purpose, wide compatibility |
| WMMA | FP16->FP32 | SM >= 7.0 | High throughput with Tensor Cores |
| DP4A | INT8->INT32 | SM >= 6.1 | Quantized inference |

### Autotuning Registry

Thread-safe cache mapping (M, N, K, SM) to the best-performing kernel configuration, with sensible defaults based on SM version.

## Usage Examples

See the `test/` directory for comprehensive usage examples:

- `test/unit/kernels/test_gemm_simt.cu` - SIMT correctness and epilogue tests
- `test/unit/kernels/test_gemm_wmma_tc.cu` - WMMA correctness with fp16 tolerance
- `test/unit/kernels/test_autotune.cu` - Registry API tests

## Building Documentation

From the build directory:
```bash
ninja doxygen_86_Core_Common_API
```

The generated HTML documentation will be available at:
```
build/80.Transformer/86.Core_Common_API/doxygen/html/index.html
```

## Dependencies

- **89.Tensor_Ops_Common_API** - Vector I/O and layout swizzle utilities
- **CudaCustomLib** - CUDA utility functions
- CUDA Toolkit (WMMA requires SM >= 7.0, DP4A requires SM >= 6.1)

## Performance Considerations

- SIMT GEMM uses 32x32 tiles with 8-deep K-tiles for shared memory reuse
- WMMA GEMM operates on 16x16x16 fragments matching hardware tile size
- INT8 DP4A processes 4 elements per instruction for 4x throughput over FP32
- Epilogue fusion eliminates separate kernel launch overhead for bias/activation/residual

## See Also

- Module README.md for detailed learning materials
- Test files for usage examples
- Related modules: 81.Core_GEMM_Operations, 89.Tensor_Ops_Common_API
