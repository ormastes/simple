# Part 86: Core Common API
**Goal**: Provide hand-rolled GEMM backends (SIMT, WMMA Tensor Core, INT8 DP4A) with fused epilogue operations and a runtime autotuning registry for transformer inference.

## Project Structure
```
86.Core_Common_API/
├── CMakeLists.txt
├── README.md
├── doxygen/
│   ├── Doxyfile.in
│   └── mainpage.md
├── src/
│   ├── CMakeLists.txt
│   ├── common/
│   │   ├── epilogue_kernels.cuh      # Fused bias/activation/residual epilogue
│   │   └── autotune_registry.cuh     # Shape-to-kernel cache interface
│   └── kernels/
│       ├── gemm_simt.cu              # Shared-memory tiled SIMT GEMM (fp32)
│       ├── gemm_wmma_tc.cu           # Tensor Core WMMA GEMM (fp16->fp32)
│       ├── gemm_int8_dp4a.cu         # INT8 DP4A GEMM
│       └── autotune_registry.cu      # Autotuning registry implementation
└── test/
    ├── CMakeLists.txt
    └── unit/
        └── kernels/
            ├── test_gemm_simt.cu      # SIMT correctness + epilogue tests
            ├── test_gemm_wmma_tc.cu   # WMMA correctness tests
            └── test_autotune.cu       # Autotuning registry tests
```

## Quick Navigation
- [86.1 Epilogue Fusion](#861-epilogue-fusion)
- [86.2 SIMT GEMM](#862-simt-gemm)
- [86.3 WMMA Tensor Core GEMM](#863-wmma-tensor-core-gemm)
- [86.4 INT8 DP4A](#864-int8-dp4a)
- [86.5 Autotuning](#865-autotuning)
- [86.6 Summary](#866-summary)
- [Build & Run](#build--run)

---

## **86.1 Epilogue Fusion**
Epilogue fusion eliminates separate kernel launches for post-GEMM operations by folding bias addition, activation functions, and residual connections directly into the GEMM output store.

### **86.1.1 Epilogue Configuration**
The `Epilogue` struct controls which post-GEMM operations are applied and in what order.

```cpp
// src/common/epilogue_kernels.cuh
struct Epilogue {
    bool has_bias;       // Add bias vector
    bool has_residual;   // Add residual connection
    Activation act;      // GELU, SiLU, ReLU, or None
    float scale;         // Output scaling factor
};
```
**Key Points**:
- Order of operations: `scale * act(gemm_output + bias) + residual`
- Default configuration applies no transformations (identity epilogue)
- All activation functions are implemented as `__device__ __forceinline__` for zero overhead

**Source**: `src/common/epilogue_kernels.cuh`

### **86.1.2 Supported Activations**
Three activation functions are provided, covering the most common transformer architectures.

| Activation | Formula | Use Case |
|-----------|---------|----------|
| GELU | `x * 0.5 * (1 + tanh(sqrt(2/pi) * (x + 0.044715 * x^3)))` | GPT, BERT |
| SiLU/Swish | `x / (1 + exp(-x))` | LLaMA, Mistral |
| ReLU | `max(0, x)` | Classic architectures |

### **86.1.3 Standalone Epilogue Kernel**
A standalone `epilogue_kernel` is provided for cases where the GEMM and epilogue must run separately (e.g., when using cuBLAS for GEMM).

```cpp
// Apply epilogue to pre-computed GEMM output
epilogue_kernel<<<grid, block>>>(C, bias, residual, M, N, ep);
```
**Source**: `src/common/epilogue_kernels.cuh`

---

## **86.2 SIMT GEMM**
The SIMT GEMM provides a shared-memory tiled matrix multiplication that runs on all CUDA-capable GPUs without requiring Tensor Core hardware.

### **86.2.1 Tiling Strategy**
The kernel uses 32x32 output tiles with 8-deep K-dimension tiles to maximize shared memory reuse while keeping register pressure manageable.

```cpp
// src/kernels/gemm_simt.cu
#define TILE_M 32
#define TILE_N 32
#define TILE_K 8

__shared__ float As[TILE_M][TILE_K];
__shared__ float Bs[TILE_K][TILE_N];
```
**Key Points**:
- Each thread block computes a 32x32 output tile
- K-dimension is tiled at 8 to balance shared memory usage and arithmetic intensity
- Boundary conditions handle non-tile-aligned matrix dimensions
- Epilogue is fused directly into the output store

**Source**: `src/kernels/gemm_simt.cu`

### **86.2.2 Launch Interface**

```cpp
void simt_gemm_fp32(float* C, const float* A, const float* B,
                    int M, int N, int K, Epilogue ep,
                    const float* bias, const float* residual,
                    cudaStream_t stream);
```
**Source**: `src/kernels/gemm_simt.cu`

---

## **86.3 WMMA Tensor Core GEMM**
The WMMA GEMM leverages Tensor Core hardware (SM >= 7.0) for high-throughput fp16 matrix multiplication with fp32 accumulation.

### **86.3.1 WMMA Fragment Layout**
Each warp processes one 16x16x16 fragment using hardware matrix multiply-accumulate instructions.

```cpp
// src/kernels/gemm_wmma_tc.cu
wmma::fragment<wmma::matrix_a, 16, 16, 16, half, wmma::row_major> a_frag;
wmma::fragment<wmma::matrix_b, 16, 16, 16, half, wmma::row_major> b_frag;
wmma::fragment<wmma::accumulator, 16, 16, 16, float> c_frag;
```
**Key Points**:
- Input matrices are fp16, accumulation is fp32 for numerical stability
- Each warp computes one 16x16 output tile via `wmma::mma_sync`
- 4 warps per block (128 threads) for sufficient occupancy
- Requires SM >= 7.0 (Volta, Turing, Ampere, Hopper)

**Source**: `src/kernels/gemm_wmma_tc.cu`

### **86.3.2 Launch Interface**

```cpp
void wmma_gemm_fp16(float* C, const half* A, const half* B,
                    int M, int N, int K, cudaStream_t stream);
```
**Source**: `src/kernels/gemm_wmma_tc.cu`

---

## **86.4 INT8 DP4A**
The INT8 GEMM uses DP4A intrinsics for quantized inference, achieving up to 4x throughput over fp32 by processing four int8 multiplications in a single instruction.

### **86.4.1 DP4A Intrinsic**
The `__dp4a` instruction computes a dot product of four packed int8 values, accumulating into int32.

```cpp
// src/kernels/gemm_int8_dp4a.cu
__device__ __forceinline__ int dp4a(int a, int b, int c) {
    return __dp4a(a, b, c);  // c += dot4(a_bytes, b_bytes)
}
```
**Key Points**:
- K dimension must be a multiple of 4
- B matrix is stored transposed (column-major) for contiguous DP4A access
- Output is int32; dequantization to float is done externally
- Requires SM >= 6.1 (Pascal and newer)

**Source**: `src/kernels/gemm_int8_dp4a.cu`

### **86.4.2 Launch Interface**

```cpp
void gemm_i8_dp4a(int32_t* C, const int8_t* A, const int8_t* B,
                  int M, int N, int K, cudaStream_t stream);
```
**Source**: `src/kernels/gemm_int8_dp4a.cu`

---

## **86.5 Autotuning**
The autotuning registry provides a thread-safe cache that maps problem shapes to the best-performing kernel configuration, enabling runtime kernel selection.

### **86.5.1 Configuration Keys**
Configs are indexed by `(M, N, K, SM version)`, so the same problem size can have different optimal kernels on different GPU architectures.

```cpp
// src/common/autotune_registry.cuh
struct GemmConfig {
    int M, N, K;
    GemmKernel kernel;       // SIMT_FP32, WMMA_FP16, or INT8_DP4A
    int tile_m, tile_n, tile_k;
    int sm_version;
};
```
**Source**: `src/common/autotune_registry.cuh`

### **86.5.2 Registry API**
The registry provides three operations: lookup, register, and clear.

```cpp
GemmConfig get_best_config(int M, int N, int K, int sm);  // Lookup or default
void register_config(const GemmConfig& config);             // Cache a result
void clear_autotune_cache();                                 // Reset cache
```

**Key Points**:
- Default heuristic: WMMA for SM >= 70, SIMT for older GPUs
- Thread-safe via `std::mutex` (host-side only)
- Cache is process-global; cleared between benchmark runs

**Source**: `src/kernels/autotune_registry.cu`

---

## **86.6 Summary**

- **Key Takeaways**:
  - Three GEMM backends cover fp32, fp16, and int8 precision levels
  - Epilogue fusion eliminates separate kernel launches for bias/activation/residual
  - WMMA Tensor Cores deliver significantly higher throughput on SM >= 7.0 hardware
  - DP4A enables 4x int8 throughput for quantized inference workloads
  - Runtime autotuning selects the best kernel for each problem shape and GPU

- **Performance Characteristics**:
  - SIMT: ~1-5 TFLOPS depending on matrix size and GPU
  - WMMA: ~20-40 TFLOPS on Tensor Core hardware (fp16)
  - DP4A: ~4x throughput over fp32 for int8 workloads

- **Common Errors**:

  | Error | Cause | Solution |
  |-------|-------|----------|
  | WMMA kernel produces zeros | SM < 7.0 GPU | Use SIMT backend or upgrade GPU |
  | DP4A wrong results | K not multiple of 4 | Pad K to multiple of 4 |
  | Large fp16 error | Values outside fp16 range | Scale inputs to [-1, 1] range |
  | Epilogue NaN | SiLU with large negative input | Check input range |

- **Next Steps**: [81.Core_GEMM_Operations](../81.Core_GEMM_Operations/README.md) for higher-level GEMM dispatch and tiling strategies

- **References**:
  - [CUDA WMMA API](https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#wmma)
  - [CUTLASS GEMM](https://github.com/NVIDIA/cutlass)
  - [DP4A Whitepaper](https://developer.nvidia.com/blog/mixed-precision-programming-cuda-8/)

---

## Build & Run

```bash
# From the repository build directory
cmake --preset default
ninja 86_Core_Common_API_test

# Run tests
./80.Transformer/86.Core_Common_API/86_Core_Common_API_test

# Generate documentation
ninja doxygen_86_Core_Common_API
```
