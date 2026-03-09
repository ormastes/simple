# Module 76: PyTorch C API Integration

## Overview

This module implements a C API layer that bridges custom CUDA kernels with PyTorch via Python ctypes.
The architecture exposes GPU-accelerated operations through a stable C ABI, allowing PyTorch users to
call custom CUDA kernels without compiling C++ extensions or depending on the PyTorch C++ API.

## Module Architecture

The module is organized into three layers:

- **c_api/**: C-linkage API functions with TorchTensorDesc-based interface
  - `torch_api.h` - Public header with status codes, tensor descriptors, and function declarations
  - `torch_matmul_api.cpp` - Matrix multiplication C API (validates inputs, calls kernel launcher)
  - `torch_backprop_api.cpp` - Linear layer forward/backward C API
  - `torch_attention_api.cpp` - Scaled dot-product attention C API

- **kernels/**: CUDA kernel implementations and host-side launch wrappers
  - `matmul_kernel.cu` - Tiled 32x32 matmul with shared memory, softmax, bias, causal mask, row reduction
  - `matmul_kernel.h` - Host-callable launcher declarations

- **python/**: PyTorch integration layer
  - `torch_wrapper.py` - torch.autograd.Function classes wrapping the C API via ctypes

## Key Components

### C API (torch_api.h)

- `TorchTensorDesc` - Lightweight tensor descriptor (data pointer, shape, ndim, numel)
- `TorchStatus` - Error code enum (SUCCESS, INVALID_ARGUMENT, CUDA, OUT_OF_MEMORY)
- `torch_matmul()` - Tiled GPU matmul
- `torch_linear_forward()` / `torch_linear_backward()` - Linear layer with optional bias
- `torch_scaled_dot_product_attention()` - SDPA with optional causal mask

### CUDA Kernels

- `tiled_matmul_kernel` - 32x32 shared-memory tiled matrix multiplication
- `add_bias_kernel` - Row-wise bias addition
- `softmax_kernel` - Numerically stable row-wise softmax
- `causal_mask_kernel` - Upper-triangle masking for causal attention
- `reduce_rows_kernel` - Column-sum reduction for gradient computation

### Python Wrappers

- `CUDAMatMul` - torch.autograd.Function for matrix multiplication
- `CUDALinear` - torch.autograd.Function for linear layer (forward + backward)
- `CUDAScaledDotProductAttention` - torch.autograd.Function for attention

## Usage Examples

See the `test/` directory for comprehensive usage examples:

- `test/unit/test_torch_api.cu` - C API correctness tests
- `test/unit/test_matmul_kernel.cu` - Kernel-level tests (tile alignment, boundary cases)

## Building Documentation

From the build directory:
```bash
ninja doxygen_76_PyTorch_C_API
```

The generated HTML documentation will be available at:
```
build/70.GPU_Optimization/76.PyTorch_C_API/doxygen/html/index.html
```

## Dependencies

- CUDA Toolkit (cudart)
- CudaCustomLib (shared project utilities)
- GoogleTest (for unit tests)
- Python 3 + PyTorch (optional, for Python wrapper)

## Performance Considerations

- The tiled matmul uses 32x32 shared memory tiles, achieving good occupancy on most architectures
- Transpose operations in attention and linear backward currently use host-side copies; a device transpose kernel would improve throughput for large tensors
- The softmax kernel processes one row per thread, which is efficient for moderate sequence lengths

## See Also

- Module README.md for detailed learning materials
- Module 77 (PyTorch_Native_CUDA) for the pybind11/CUDAExtension approach
- Module 71 (MatMul_CPU_PyCUDA) for CPU baseline comparison
