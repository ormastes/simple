# Module 73: 73.Attention_CPU_PyCUDA

## Overview

This module implements CPU-based attention mechanisms for transformer models, serving as performance baselines for GPU comparison with PyCUDA Python bindings.

## Module Architecture

The module is organized into the following components:

- **kernels/**: CPU attention mechanism implementations
  - Scaled dot-product attention (SDPA) - naive and causal variants
  - Multi-head attention with output projection
  - Parallel SDPA with OpenMP
  - Numerically stable softmax

- **python/**: PyCUDA-compatible Python wrappers
  - ctypes-based bindings loading libcpu_attention.so
  - NumPy-compatible interface for attention operations
  - Performance benchmarking scripts

## Key Components

### Core APIs

- `cpu_sdpa_naive()` - Scaled dot-product attention: softmax(Q*K^T / sqrt(d_k)) * V
- `cpu_sdpa_causal()` - Causal (masked) attention for autoregressive models
- `cpu_multi_head_attention()` - Multi-head attention with head splitting and W_O projection
- `cpu_sdpa_parallel()` - OpenMP-parallelized SDPA across sequence positions
- `cpu_softmax()` - Numerically stable row-wise softmax
- `cpu_attention_timed()` - Timed attention dispatch returning milliseconds

### Data Structures

- Q, K, V matrices: `[seq_len x d_model]` for single-head, `[batch_size x seq_len x d_model]` for multi-head
- Attention scores: `[seq_len x seq_len]` intermediate matrix (quadratic in sequence length)
- W_O projection: `[d_model x d_model]` output projection weight matrix

### Python Interface

- `CPUAttention.sdpa(Q, K, V)` - Scaled dot-product attention
- `CPUAttention.sdpa_causal(Q, K, V)` - Causal masked attention
- `CPUAttention.multi_head(Q, K, V, W_O, num_heads)` - Multi-head attention
- `CPUAttention.softmax(input)` - Row-wise softmax

## Usage Examples

See the `test/` directory for comprehensive usage examples:

- `test/unit/test_cpu_attention.cu`: Unit tests for SDPA, causal mask, softmax, multi-head, and parameterized size tests

## Building Documentation

From the build directory:
```bash
ninja doxygen_73_Attention_CPU_PyCUDA
```

The generated HTML documentation will be available at:
```
build/70.GPU_Optimization/73.Attention_CPU_PyCUDA/doxygen/html/index.html
```

## Dependencies

- CUDA Toolkit (for compilation as .cu files)
- OpenMP (optional, for parallel SDPA)
- Python 3 (optional, for PyCUDA wrappers)
- GoogleTest (for unit tests)

## Performance Considerations

- Attention has O(L^2 * D) time complexity, quadratic in sequence length
- Memory usage is O(L^2) for the attention score matrix
- Causal masking saves ~50% compute but has same asymptotic complexity
- OpenMP parallelization provides 2-4x speedup across sequence positions
- GPU implementations (Part 78+) will be 50-500x faster

## See Also

- Module README.md for detailed learning materials
- Test files for usage examples
- Related modules: Part 71 (MatMul_CPU_PyCUDA), Part 78 (Progressive Optimizations)
