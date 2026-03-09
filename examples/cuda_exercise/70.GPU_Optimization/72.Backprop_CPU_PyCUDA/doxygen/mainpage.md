# Module 72: 72.Backprop_CPU_PyCUDA

## Overview

This module implements CPU-based backpropagation for neural network training as a performance baseline, with PyCUDA bindings for Python integration and comparison with GPU implementations.

## Module Architecture

The module is organized into the following components:

- **kernels/**: CPU backpropagation implementations
  - Forward pass for fully connected layers (naive and OpenMP-parallel)
  - Backward pass with gradient computation for input, weights, and bias
  - Activation functions (ReLU, Sigmoid) and their gradients
  - Timed forward+backward pass for benchmarking

- **python/**: PyCUDA Python wrapper and benchmarking
  - ctypes-based Python bindings for all C functions
  - NumPy-compatible interface for seamless ML workflow integration
  - Performance benchmarking and validation against NumPy

## Key Components

### Core APIs

- `cpu_forward()` - Naive forward pass: output = input * weights^T + bias
- `cpu_backward()` - Naive backward pass: compute grad_input, grad_weights, grad_bias
- `cpu_forward_parallel()` - OpenMP-parallelized forward pass
- `cpu_backward_parallel()` - OpenMP-parallelized backward pass
- `cpu_relu_forward()` / `cpu_relu_backward()` - ReLU activation and gradient
- `cpu_sigmoid_forward()` / `cpu_sigmoid_backward()` - Sigmoid activation and gradient
- `cpu_forward_backward_timed()` - Timed forward+backward pass for benchmarking

### Data Structures

All functions operate on flat float arrays in row-major order:
- Input: [batch_size x input_dim]
- Weights: [output_dim x input_dim]
- Bias: [output_dim]
- Output: [batch_size x output_dim]

### Python Wrapper

The `CPUBackprop` class provides static methods wrapping all C functions with NumPy array I/O, input validation, and error handling.

## Usage Examples

See the `test/` directory for comprehensive usage examples:

- `test/unit/test_cpu_backprop.cu`: Unit tests for forward, backward, ReLU, Sigmoid, parallel, and parameterized size tests

## Building Documentation

From the build directory:
```bash
ninja doxygen_72_Backprop_CPU_PyCUDA
```

The generated HTML documentation will be available at:
```
build/70.GPU_Optimization/72.Backprop_CPU_PyCUDA/doxygen/html/index.html
```

## Dependencies

- CUDA Toolkit (for compilation as .cu files)
- OpenMP (optional, for parallel implementations)
- Python 3 with NumPy (optional, for PyCUDA wrapper)
- GoogleTest (for unit tests)

## Performance Considerations

- Naive CPU implementation achieves ~18-60 GFLOPS depending on layer sizes
- Backward pass is ~20% more expensive than forward (3 matrix operations vs 1)
- OpenMP parallelization scales with available CPU cores
- Memory bandwidth becomes the bottleneck for large layer sizes
- GPU implementations in later modules will be 10-100x faster

## See Also

- Module README.md for detailed learning materials
- Test files for usage examples
- Related modules: 71.MatMul_CPU_PyCUDA (matrix multiplication baseline)
