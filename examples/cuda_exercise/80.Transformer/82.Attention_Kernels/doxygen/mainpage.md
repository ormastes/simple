# Module 82: Attention Kernels

## Overview

This module implements the core attention kernels for transformer inference using pure CUDA. It provides four key components: a tiled FlashAttention-style scaled dot-product attention (SDPA), rotary position embeddings (RoPE), KV cache management for autoregressive generation, and a standalone numerically stable softmax.

## Module Architecture

The module is organized into the following kernel implementations:

- **kernels/flash_attention**: Tiled scaled dot-product attention using online softmax for memory-efficient computation. Processes Q against K/V in tiles to avoid materializing the full N x N attention matrix.

- **kernels/rope**: Rotary Position Embeddings that encode absolute position information by rotating pairs of dimensions with position-dependent frequencies.

- **kernels/kv_cache**: Append and read kernels for managing the key-value cache during autoregressive inference, avoiding redundant KV computation for previous tokens.

- **kernels/softmax**: Standalone row-wise softmax with warp-level shuffle reductions for the three-phase algorithm (find max, compute exp, normalize).

## Dependencies

- `87.Attention_Common_API` -- Tile shapes, online softmax primitives, causal masks, QKV packing
- `86.Core_Common_API` -- Core GEMM backends and epilogue fusion
- `CudaCustomLib` -- Error checking and memory utilities

## Building Documentation

From the build directory:
```bash
ninja doxygen_82_Attention_Kernels
```

The generated HTML documentation will be available at:
```
build/80.Transformer/82.Attention_Kernels/doxygen/html/index.html
```

## See Also

- Module 87 (Attention Common API) for the reusable primitives consumed by these kernels
- Module 81 (Core GEMM Operations) for linear projection GEMM used before/after attention
- Module 84 (Normalization) for RMSNorm applied before attention layers
