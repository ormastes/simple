# Part 81: Core GEMM Operations
**Goal**: Provide a unified GEMM dispatcher that auto-selects between SIMT and Tensor Core WMMA backends and exposes epilogue fusion for bias + activation patterns common in transformer inference.

## Project Structure
```
81.Core_GEMM_Operations/
├── CMakeLists.txt
├── README.md
├── doxygen/
│   ├── Doxyfile.in
│   └── mainpage.md
├── src/
│   ├── CMakeLists.txt
│   ├── common/
│   │   ├── gemm_ops.cuh          # Unified GEMM dispatcher API
│   │   └── epilogue_fusion.cuh   # linear() and linear_gelu() wrappers
│   └── kernels/
│       └── gemm_ops.cu           # Dispatcher implementation
└── test/
    ├── CMakeLists.txt
    └── unit/
        └── kernels/
            └── test_gemm_ops.cu
```

## Quick Navigation
- [81.1 GEMM Dispatcher](#811-gemm-dispatcher)
- [81.2 Epilogue Fusion API](#812-epilogue-fusion-api)
- [81.3 Summary](#813-summary)
- [Build & Run](#build--run)

---

## **81.1 GEMM Dispatcher**
The dispatcher routes matrix multiply calls to the best available backend without requiring the caller to know which hardware path is optimal. This decouples computation modules (MLP, Attention) from low-level kernel selection.

### **81.1.1 GemmParams Configuration**
The `GemmParams` struct carries all information needed to select and launch a GEMM.

```cpp
// gemm_ops.cuh - Unified parameter struct
struct GemmParams {
    int M, N, K;
    const float* A_fp32;   const half* A_fp16;
    const float* B_fp32;   const half* B_fp16;
    float* C;
    bool use_tensor_cores;
    cudaStream_t stream;
};
```

**Key Points**:
- Set `A_fp16`/`B_fp16` and `use_tensor_cores=true` for WMMA Tensor Core path
- Set `A_fp32`/`B_fp32` for SIMT shared-memory path
- Output is always fp32 regardless of input precision

**Source**: `src/common/gemm_ops.cuh`

### **81.1.2 Backend Selection Logic**
The `gemm()` function inspects pointers and the `use_tensor_cores` flag to route to the appropriate Module 86 backend.

```cpp
// gemm_ops.cu - Dispatch logic
void gemm(const GemmParams& params) {
    if (params.use_tensor_cores && params.A_fp16 && params.B_fp16) {
        wmma_gemm_fp16(params.C, params.A_fp16, params.B_fp16,
                       params.M, params.N, params.K, params.stream);
    } else if (params.A_fp32 && params.B_fp32) {
        Epilogue ep;
        simt_gemm_fp32(params.C, params.A_fp32, params.B_fp32,
                       params.M, params.N, params.K, ep, nullptr, nullptr, params.stream);
    }
}
```

**Key Points**:
- WMMA path requires dimensions aligned to 16 (hardware constraint)
- SIMT path supports arbitrary dimensions via shared-memory tiling
- Epilogue (bias, activation, residual) is fused into the SIMT store phase

**Source**: `src/kernels/gemm_ops.cu`

### **81.1.3 GEMM with Fused Bias + Activation**
The `gemm_with_bias_act` function combines GEMM, bias addition, and optional GELU into a single kernel launch by configuring the epilogue struct.

```cpp
// gemm_ops.cu
void gemm_with_bias_act(float* C, const float* A, const float* B,
                        const float* bias, int M, int N, int K,
                        bool use_gelu, cudaStream_t stream) {
    Epilogue ep;
    ep.has_bias = (bias != nullptr);
    ep.act = use_gelu ? Activation::GELU : Activation::None;
    simt_gemm_fp32(C, A, B, M, N, K, ep, bias, nullptr, stream);
}
```

---

## **81.2 Epilogue Fusion API**
Convenience wrappers map common neural network layer patterns to the GEMM dispatcher, making call sites more readable and less error-prone.

### **81.2.1 Linear Layer**
Standard dense projection used for Q/K/V projections, output projections, and FFN layers.

```cpp
// epilogue_fusion.cuh
inline void linear(float* output, const float* input, const float* weights,
                   const float* bias, int batch, int in_dim, int out_dim,
                   cudaStream_t stream = 0) {
    gemm_with_bias_act(output, input, weights, bias, batch, out_dim, in_dim, false, stream);
}
```

### **81.2.2 Linear + GELU**
Fused projection + activation for the first FFN layer in GPT-style transformers.

```cpp
// epilogue_fusion.cuh
inline void linear_gelu(float* output, const float* input, const float* weights,
                        const float* bias, int batch, int in_dim, int out_dim,
                        cudaStream_t stream = 0) {
    gemm_with_bias_act(output, input, weights, bias, batch, out_dim, in_dim, true, stream);
}
```

**Key Points**:
- Single kernel launch for matmul + bias + activation -- no intermediate buffer
- Reduces global memory traffic compared to separate GEMM and pointwise kernels

**Source**: `src/common/epilogue_fusion.cuh`

---

## **81.3 Summary**

- **Key Takeaways**:
  - The GEMM dispatcher decouples computation modules from low-level kernel selection
  - WMMA Tensor Core path gives higher throughput for fp16 inputs on supported hardware
  - Epilogue fusion (bias + activation) reduces memory bandwidth by combining operations into the GEMM store phase
  - Convenience wrappers (`linear`, `linear_gelu`) simplify call sites for common patterns

- **Performance Characteristics**:
  - SIMT GEMM: memory-bound for small matrices, compute-bound for large matrices (>256x256)
  - WMMA GEMM: up to 8x throughput vs SIMT on Tensor Core hardware (Volta+)
  - Fused epilogue: saves one full read+write pass over the output matrix

- **Common Errors**:

  | Error | Cause | Solution |
  |---|---|---|
  | Incorrect results with WMMA | Dimensions not multiple of 16 | Pad M, N, K to multiples of 16 |
  | Null pointer dereference | Both fp32 and fp16 pointers are nullptr | Set at least one pair of input pointers |
  | Wrong output with bias | Bias vector length != N | Ensure bias has exactly N elements |

- **Next Steps**: [83.MLP](../83.MLP/README.md) -- uses `linear` and `linear_gelu` for feed-forward network layers

- **References**:
  - [CUDA WMMA API](https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#wmma)
  - [86.Core_Common_API](../86.Core_Common_API/README.md) -- backend GEMM implementations

---

## Build & Run

```bash
# From the repository build directory
cmake --build . --target 81_Core_GEMM_Operations_test
ctest -R 81_Core_GEMM_Operations

# Generate documentation
ninja doxygen_81_Core_GEMM_Operations
```
