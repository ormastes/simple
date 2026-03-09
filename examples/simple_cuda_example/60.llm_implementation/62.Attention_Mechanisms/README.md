# Attention Mechanisms

**Tier:** 2 (Concept Adaptation)
**Original CUDA Concept:** Self-attention kernel (Q*K^T/sqrt(d), softmax, V multiplication)

## Simple Approach

Simple implements self-attention using GPU kernels with compile-time dimension checking.
The `Tensor<rows, cols>` type system ensures Q, K, V matrices have compatible dimensions,
catching shape errors at compile time rather than runtime.

Key features:
- **Dimension checking:** `Tensor<seq_len, head_dim>` validates shapes at compile time
- **Softmax kernel:** Numerically stable (max subtraction) parallel softmax
- **Scaling:** Automatic `1/sqrt(d_k)` scaling in attention score computation
- **Masking:** Causal mask support for autoregressive models

## Concepts Covered

- Query, Key, Value projection
- Scaled dot-product attention: softmax(QK^T / sqrt(d_k)) * V
- Numerically stable softmax on GPU
- Causal (autoregressive) masking
- Multi-head attention split/concat

## Files

- `main.spl` - Self-attention kernels with dimension checking
- `spec.spl` - Tests for attention correctness
