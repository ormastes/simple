# Module 74: 74.Experts_CPU_PyCUDA

## Overview

This module implements CPU-based Mixture of Experts (MoE) layers for sparse neural networks, serving as a performance baseline for GPU comparison with PyCUDA bindings for Python integration.

## Module Architecture

The module is organized into the following components:

- **kernels/**: CPU MoE implementations
  - Top-k gating with softmax normalization
  - Single expert FFN with GELU activation
  - Complete MoE forward pass (naive and OpenMP parallel)
  - Flat buffer layout for all expert weights

- **python/**: PyCUDA wrapper and benchmarking
  - ctypes-based Python bindings (CPUMoE class)
  - Performance benchmarking across configurations
  - Validation against NumPy reference

## Key Components

### Core APIs

- `cpu_topk_gating()` - Softmax-based top-k expert selection
- `cpu_expert_ffn()` - Single expert feed-forward network with GELU
- `cpu_moe_forward()` - Complete MoE forward pass (naive)
- `cpu_moe_forward_parallel()` - OpenMP-parallelized MoE forward
- `cpu_gelu()` - GELU activation function
- `cpu_moe_timed()` - Timed MoE forward for benchmarking

### Data Layout

Expert weights use flat buffer layout for simple ctypes interop:
- W1: `[num_experts, d_ff, d_model]`
- b1: `[num_experts, d_ff]`
- W2: `[num_experts, d_model, d_ff]`
- b2: `[num_experts, d_model]`

### Python Interface

The `CPUMoE` class provides NumPy-compatible methods:
- `CPUMoE.topk_gating(gate_logits, top_k)` - Expert selection
- `CPUMoE.expert_ffn(input, W1, b1, W2, b2, expert_idx, num_experts)` - Single expert
- `CPUMoE.moe_forward(input, gate_weights, W1, b1, W2, b2, top_k)` - Full MoE
- `CPUMoE.gelu(input)` - GELU activation

## Usage Examples

See the `test/` directory for comprehensive usage examples:

- `test/unit/test_cpu_experts.cu`: Unit tests for all MoE components

## Building Documentation

From the build directory:
```bash
ninja doxygen_74_Experts_CPU_PyCUDA
```

The generated HTML documentation will be available at:
```
build/70.GPU_Optimization/74.Experts_CPU_PyCUDA/doxygen/html/index.html
```

## Dependencies

- CUDA Toolkit (for .cu compilation)
- OpenMP (optional, for parallel implementation)
- Python3 (optional, for PyCUDA wrappers)
- GoogleTest (for unit tests)

## Performance Considerations

- Flat buffer layout avoids pointer-of-pointer indirection for ctypes
- OpenMP parallelization over batch dimension
- Expert switching causes cache misses with many experts
- GELU is more expensive than ReLU but standard in transformers
- GPU implementations (Part 78) will show 10-100x speedup

## See Also

- Module README.md for detailed learning materials
- Test files for usage examples
- Related modules: 71.MatMul_CPU_PyCUDA (same pattern), 78.Progressive_Optimizations
