Here’s the **updated version** of that document with the removed primitive helper modules (`error_check.cuh`, `cp_async_utils.cuh`, `arch_traits.cuh`, `dtype.cuh`) — replaced by direct CUDA built-ins and runtime APIs.

---

# 🚀 Minimal CUDA LLM Backend (No cuBLAS/cuDNN/CUTLASS)

This version implements all math as **pure CUDA kernels** (SIMT + WMMA/Tensor Cores) and uses only standard CUDA runtime / headers (`<cuda_runtime.h>`, `<cuda_fp16.h>`, `<cuda_bf16.h>`, `<cuda/pipeline>`).

---

```
cuda/
  core/
    gemm_ops.cu                # calls our SIMT/WMMA kernels (no cuBLAS)
    gemm_ops.cuh
    epilogue_fusion.cuh        # bias/residual/activation fusers for GEMM epilogues

    # Hand-rolled GEMM backends
    gemm_wmma_tc.cu            # Tensor Core WMMA (fp16/bf16→fp32)
    gemm_simt.cu               # Shared-mem SIMT fallback (fp32/fp16)
    gemm_int8_dp4a.cu          # (optional) int8×int8→int32 GEMM (DP4A)
    epilogue_kernels.cuh       # Fused bias+activation+residual store
    autotune_registry.cu       # Shape→kernel/tile cache
    autotune_registry.cuh

  attention/
    flash_attention.cu         # Fused SDPA kernel (FlashAttention-style)
    flash_attention.cuh
    rope.cu
    rope.cuh
    kv_cache.cu
    kv_cache.cuh
    softmax.cu
    softmax.cuh

    # Helpers for SDPA kernels
    sdpa_tiles.cuh             # Tile shapes, MMA layouts
    online_softmax.cuh         # Numerically stable streaming softmax
    causal_mask.cuh            # Causal/padding mask predication
    qkv_packing.cuh            # Pack/unpack/interleave Q,K,V layouts

  mlp/
    activation.cu
    activation.cuh

  norms/
    rmsnorm.cu
    rmsnorm.cuh

    # Norm building blocks
    reduce_warp.cuh            # Warp-level reduce (shfl_xor)
    reduce_block.cuh           # Block-level reduce (shared mem)
    mean_rsqrt.cuh             # Mean + rsqrt helpers for RMSNorm

  tensor_ops/
    bias_residual.cu
    bias_residual.cuh
    transpose_permute.cu
    transpose_permute.cuh

    # Tensor movement utilities
    vector_io.cuh              # Vectorized ld/st (float2/float4/half2)
    layout_swizzle.cuh         # Col32/RowMajor/LD padded strides; KV-cache layout
```

---

## 🔧 Primitive utilities (now removed)

These headers have been removed; use **CUDA built-ins** directly:

| Removed header       | Use instead                                                |
| -------------------- | ---------------------------------------------------------- |
| `error_check.cuh`    | `cudaGetLastError()`, `cudaPeekAtLastError()`              |
| `cp_async_utils.cuh` | `<cuda/pipeline>` → `cuda::pipeline`, `cuda::memcpy_async` |
| `arch_traits.cuh`    | `cudaGetDeviceProperties()` for `sm_major`, `sm_minor`     |
| `dtype.cuh`          | `<cuda_fp16.h>` and `<cuda_bf16.h>` for conversions        |

> ✅ **Tip:** You can query architecture info at runtime once and pass to your autotuner.

---

## 🧩 What each module does

### core/ (GEMM without cuBLAS)

* **`gemm_wmma_tc.cu`**

  * `void wmma_gemm_fp16(const half* A, const half* B, float* C, int M,int N,int K, bool transA,bool transB, Epilogue ep);`
  * Implements Tensor Core WMMA fragments with shared memory tiling.

* **`gemm_simt.cu`**

  * `void simt_gemm_fp32(const float* A, const float* B, float* C, int M,int N,int K, Epilogue ep);`
  * Plain SIMT kernel using shared memory and double-buffering.

* **`gemm_int8_dp4a.cu`**

  * (optional) `void gemm_i8_dp4a(const int8_t* A, const int8_t* B, int32_t* C, int M,int N,int K, Dequant dq);`
  * INT8 matrix multiply via DP4A intrinsics.

* **`epilogue_kernels.cuh`**

  * Defines:

    ```cpp
    struct Epilogue {
      bool bias,residual;
      enum Act { None, GELU, SiLU } act;
      float scale;
    };
    ```
  * Inline fused bias/add/activation kernels.

* **`autotune_registry.{cu,cuh}`**

  * Stores best tile shape and kernel variant per `(M,N,K,dtype,sm)`.

---

### attention/ (Fused SDPA without cuDNN)

* **`sdpa_tiles.cuh`** — compile-time MMA tile configs and smem layout constants.
* **`online_softmax.cuh`** — streaming reduction for stable softmax.
* **`causal_mask.cuh`** — simple device predicate:

  ```cpp
  __device__ bool causal_keep(int q, int k) { return k <= q; }
  ```
* **`qkv_packing.cuh`** — reorder `[B,T,H,D] <-> [B,H,T,D]` efficiently with vectorized I/O.

---

### norms/ (shared utilities)

* **`reduce_warp.cuh`** — warp-level sum/max reductions via `__shfl_xor_sync`.
* **`reduce_block.cuh`** — cooperative block reductions using shared memory.
* **`mean_rsqrt.cuh`** — compute mean and reciprocal RMS for normalization.

---

### tensor_ops/ (movement and layout)

* **`vector_io.cuh`** — vectorized load/store templates (float4/half2) with alignment guards.
* **`layout_swizzle.cuh`** — row/column-major or Col32 strides for padded layouts, used by GEMM/attention.

---

## 🔄 Dataflow Map

| Operation         | Module                                                              |
| ----------------- | ------------------------------------------------------------------- |
| Linear (matmul)   | `gemm_ops` → `gemm_wmma_tc` or `gemm_simt` → `epilogue_kernels`     |
| Attention         | `flash_attention` → `sdpa_tiles` + `online_softmax` + `causal_mask` |
| RoPE              | `rope.cu`                                                           |
| RMSNorm           | `rmsnorm.cu` → `reduce_*` + `mean_rsqrt`                            |
| Transpose/Reorder | `transpose_permute` + `vector_io`                                   |
| KV cache          | `kv_cache.cu` (internally uses `layout_swizzle`)                    |

---

## 🧱 Build flags & architecture notes

* **Target:**

  ```bash
  -gencode arch=compute_80,code=sm_80 \
  -gencode arch=compute_90,code=sm_90
  ```
* **Recommended:**

  * `-use_fast_math` for elementwise ops
  * `#if __CUDA_ARCH__ >= 800` for WMMA / cp.async paths
  * `-DTRANSFORMER_USE_WMMA=1` to prefer Tensor Cores when available

---

## ✅ First implementation order

1. `simt_gemm_fp32` → connect to `gemm_ops`.
2. `wmma_gemm_fp16` → verify correctness and performance.
3. `flash_attention.cu` → implement core QKᵀ, softmax, PV (without cp.async first).
4. `rmsnorm.cu` → integrate warp/block reducers.
5. `autotune_registry` → store and reuse tile/kernel preferences.

---

Would you like me to regenerate this as a **Markdown doc (README.md)** you can place under `cuda/README.md`? I can include section headings, code block formatting, and TODO placeholders for each kernel.
