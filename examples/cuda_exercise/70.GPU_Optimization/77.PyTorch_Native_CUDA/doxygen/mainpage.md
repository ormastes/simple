# Module 77: PyTorch Native CUDA Extensions

## Overview

This module implements PyTorch native CUDA extensions using torch.utils.cpp_extension, providing custom GPU operators for matrix multiplication, linear layer backward pass, and scaled dot-product attention. It demonstrates the full workflow from raw CUDA kernels through pybind11 bindings to torch.autograd.Function wrappers.

## Module Architecture

The module is organized into the following components:

- **src/cuda/**: Core CUDA kernel implementations
  - `matmul_cuda.cu` - Tiled 32x32 shared-memory matrix multiplication
  - `backprop_cuda.cu` - Fused linear layer forward and backward kernels
  - `attention_cuda.cu` - Scaled dot-product attention with optional causal mask
  - `native_ops.h` - Host-callable launcher declarations

- **src/cpp/**: PyTorch pybind11 bindings
  - `bindings.cpp` - Tensor validation, pointer extraction, and Python module registration

- **src/python/**: Python-level operator wrappers
  - `operators.py` - torch.autograd.Function classes with forward/backward
  - `jit_extensions.py` - JIT compilation via torch.utils.cpp_extension.load()

## Key Components

### CUDA Kernels
- `native_matmul()` - Tiled matmul with shared memory blocking
- `native_linear_forward()` / `native_linear_backward()` - Fused linear layer operations
- `native_attention()` - SDPA with causal mask, scale, and softmax

### Python Wrappers
- `NativeMatMul` - Autograd-compatible matrix multiplication
- `NativeLinear` - Autograd-compatible linear layer
- `NativeAttention` - Autograd-compatible attention

## Building

### Extension build with setup.py:
```bash
cd 70.GPU_Optimization/77.PyTorch_Native_CUDA
pip install -e .
```

### CUDA-only tests (no PyTorch dependency):
```bash
ninja 77_PyTorch_Native_CUDA_test
```

### Documentation:
```bash
ninja doxygen_77_PyTorch_Native_CUDA
```

## Dependencies

- CUDA Toolkit
- CudaCustomLib (shared utilities)
- PyTorch (optional, for Python bindings and tests)

## See Also

- Module README.md for detailed learning materials and benchmarks
- [Module 59: Production Attention with NVMe](../../50.GPU-NVMe_Interaction/59.Attention_Expert_Dynamic_Load/README.md)
- Test files for usage examples
