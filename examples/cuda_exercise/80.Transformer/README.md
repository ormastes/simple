# 🚀 80. Transformer Low-Level CUDA Kernels

> Pure CUDA kernels for transformer inference -- no cuBLAS, cuDNN, or CUTLASS dependencies. All math is implemented as hand-rolled SIMT and WMMA/Tensor Core kernels using only standard CUDA runtime headers.

---

## 🧩 Part 89: Tensor Ops Common API

**Goal**: Vectorized I/O and layout utilities for efficient GPU memory access patterns. See [89.Tensor_Ops_Common_API/README.md](89.Tensor_Ops_Common_API/README.md)
- **89.1** [Vectorized I/O](89.Tensor_Ops_Common_API/README.md#891-vectorized-io)
- **89.2** [Layout Swizzle](89.Tensor_Ops_Common_API/README.md#892-layout-swizzle)
- **89.3** [Summary](89.Tensor_Ops_Common_API/README.md#893-summary)

---

## 🧩 Part 88: Normalization Common API

**Goal**: Warp and block reduction primitives for normalization kernels. See [88.Normalization_Common_API/README.md](88.Normalization_Common_API/README.md)
- **88.1** Warp-Level Reduce (`__shfl_xor_sync`)
- **88.2** Block-Level Reduce (shared memory)
- **88.3** Mean + Reciprocal Square Root Helpers

---

## 🧩 Part 87: Attention Common API

**Goal**: Tile shapes, online softmax, causal masks, and QKV packing helpers for SDPA kernels. See [87.Attention_Common_API/README.md](87.Attention_Common_API/README.md)
- **87.1** SDPA Tile Shapes and MMA Layouts
- **87.2** Numerically Stable Online Softmax
- **87.3** Causal and Padding Mask Predication
- **87.4** QKV Pack/Unpack/Interleave

---

## 🧩 Part 86: Core Common API

**Goal**: Hand-rolled GEMM backends and epilogue fusion infrastructure. See [86.Core_Common_API/README.md](86.Core_Common_API/README.md)
- **86.1** Tensor Core WMMA GEMM (fp16/bf16 to fp32)
- **86.2** Shared-Memory SIMT GEMM Fallback (fp32/fp16)
- **86.3** INT8 DP4A GEMM (optional)
- **86.4** Fused Epilogue Kernels (bias + activation + residual)
- **86.5** Autotune Registry (shape to kernel/tile cache)

---

## 🧩 Part 85: Tensor Operations

**Goal**: Bias-residual addition, transpose, and permute operations using vectorized I/O. See [85.Tensor_Operations/README.md](85.Tensor_Operations/README.md)
- **85.1** Fused Bias + Residual Addition
- **85.2** Transpose and Dimension Permutation

---

## 🧩 Part 84: Normalization

**Goal**: RMSNorm kernel using warp/block reduction building blocks. See [84.Normalization/README.md](84.Normalization/README.md)
- **84.1** RMSNorm Implementation
- **84.2** Fused Norm + Residual Variants

---

## 🧩 Part 83: MLP

**Goal**: Activation function kernels (GELU, SiLU) for MLP layers. See [83.MLP/README.md](83.MLP/README.md)
- **83.1** GELU Activation
- **83.2** SiLU / Swish Activation
- **83.3** Fused Gate Projections

---

## 🧩 Part 82: Attention Kernels

**Goal**: Fused scaled dot-product attention (FlashAttention-style), RoPE, KV cache, and softmax. See [82.Attention_Kernels/README.md](82.Attention_Kernels/README.md)
- **82.1** Flash Attention (Fused SDPA)
- **82.2** Rotary Position Embeddings (RoPE)
- **82.3** KV Cache Management
- **82.4** Standalone Softmax

---

## 🧩 Part 81: Core GEMM Operations

**Goal**: High-level GEMM dispatcher that selects the best backend kernel. See [81.Core_GEMM_Operations/README.md](81.Core_GEMM_Operations/README.md)
- **81.1** GEMM Ops Dispatcher
- **81.2** Epilogue Fusion API

---

## ✅ Summary

This module implements the complete compute stack for transformer inference using pure CUDA kernels.

### Build Order and Dependencies

```
Layer 0 (Common APIs - no dependencies):
  89.Tensor_Ops_Common_API    -- vector_io, layout_swizzle
  88.Normalization_Common_API -- reduce_warp, reduce_block, mean_rsqrt
  87.Attention_Common_API     -- sdpa_tiles, online_softmax, causal_mask, qkv_packing

Layer 1 (Core backends - depends on Common APIs):
  86.Core_Common_API          -- gemm_wmma_tc, gemm_simt, epilogue_kernels, autotune

Layer 2 (Computation modules - depends on Common APIs + Core):
  81.Core_GEMM_Operations     -- gemm_ops dispatcher
  84.Normalization            -- rmsnorm
  85.Tensor_Operations        -- bias_residual, transpose_permute
  83.MLP                      -- activation functions
  82.Attention_Kernels        -- flash_attention, rope, kv_cache, softmax
```

### Dataflow Map

| Operation         | Module                                                           |
| ----------------- | ---------------------------------------------------------------- |
| Linear (matmul)   | `81.Core` -> `86.Core_Common` (wmma_tc or simt) -> epilogue     |
| Attention         | `82.Attention` -> `87.Attention_Common` (tiles + softmax + mask) |
| RoPE              | `82.Attention` (rope.cu)                                         |
| RMSNorm           | `84.Normalization` -> `88.Norm_Common` (reduce + mean_rsqrt)    |
| Transpose/Reorder | `85.Tensor_Ops` -> `89.Tensor_Common` (vector_io)               |
| KV cache          | `82.Attention` -> `89.Tensor_Common` (layout_swizzle)           |

### Key Design Decisions

1. **No external math libraries**: All GEMM, attention, and normalization are hand-rolled CUDA kernels
2. **Common API layer**: Reusable primitives (vectorized I/O, reductions, tile configs) shared across modules
3. **Epilogue fusion**: Bias, activation, and residual are fused into GEMM store operations to minimize memory traffic
4. **Architecture awareness**: `#if __CUDA_ARCH__ >= 800` guards for WMMA / cp.async paths

**Prerequisites**: Modules 10-49 (CUDA basics through advanced), CUDA Toolkit 13.0+, GPU with Compute Capability 7.5+

**Next Steps**: Integrate with [60.LLM_Implementation](../60.LLM_Implementation/README.md) for end-to-end inference or [70.GPU_Optimization](../70.GPU_Optimization/README.md) for performance tuning.

---
