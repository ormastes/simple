# Part 87: Attention Common API
**Goal**: Provide reusable tile shapes, online softmax, causal masks, and QKV packing helpers for scaled dot-product attention kernels.

## Project Structure
```
87.Attention_Common_API/
├── CMakeLists.txt
├── README.md
├── doxygen/
│   ├── Doxyfile.in
│   └── mainpage.md
├── src/
│   ├── CMakeLists.txt
│   └── common/
│       ├── sdpa_tiles.cuh          # Tile shapes and MMA layout constants
│       ├── sdpa_tiles.cu
│       ├── online_softmax.cuh      # Numerically stable streaming softmax
│       ├── online_softmax.cu
│       ├── causal_mask.cuh         # Causal masking predicates
│       ├── causal_mask.cu
│       ├── qkv_packing.cuh        # QKV tensor layout reordering
│       └── qkv_packing.cu
└── test/
    ├── CMakeLists.txt
    └── unit/
        └── kernels/
            ├── test_online_softmax.cu
            ├── test_causal_mask.cu
            └── test_qkv_packing.cu
```

## Quick Navigation
- [87.1 SDPA Tiles](#871-sdpa-tiles)
- [87.2 Online Softmax](#872-online-softmax)
- [87.3 Causal Masking](#873-causal-masking)
- [87.4 QKV Packing](#874-qkv-packing)
- [87.5 Summary](#875-summary)
- [Build & Run](#build--run)

---

## **87.1 SDPA Tiles**
Tile configurations define the shared memory blocking strategy for scaled dot-product attention. Different GPU architectures benefit from different tile sizes based on their shared memory capacity and warp scheduler characteristics.

### **87.1.1 SDPATileConfig Struct**
The `SDPATileConfig` struct captures the three dimensions that control attention tiling.

```cpp
// sdpa_tiles.cuh - Tile configuration for shared memory blocking
struct SDPATileConfig {
    int Br;   // Tile rows for Q (query block size)
    int Bc;   // Tile cols for K (key block size)
    int D;    // Head dimension
};
```
**Key Points**:
- `Br` determines how many query rows are processed per thread block
- `Bc` determines how many key columns are loaded per tile iteration
- `D` is the head dimension (typically 64 or 128)

**Source**: `src/common/sdpa_tiles.cuh`

### **87.1.2 Architecture-Specific Defaults**
Pre-tuned tile sizes are provided for SM75 (Turing), SM80 (Ampere), and SM86 (GA10x).

```cpp
// sdpa_tiles.cuh - Architecture-aware tile selection
constexpr SDPATileConfig sdpa_tile_sm75() { return {64, 64, 64}; }
constexpr SDPATileConfig sdpa_tile_sm80() { return {128, 64, 64}; }
constexpr SDPATileConfig sdpa_tile_sm86() { return {128, 128, 64}; }
```

### **87.1.3 Shared Memory Calculation**
The `sdpa_smem_size` function computes how many bytes of shared memory a given tile configuration requires for the Q and K tile buffers.

```cpp
// sdpa_tiles.cuh - Shared memory requirement
constexpr int sdpa_smem_size(SDPATileConfig cfg) {
    return (cfg.Br * cfg.D + cfg.Bc * cfg.D) * sizeof(float);
}
```

---

## **87.2 Online Softmax**
The online softmax algorithm computes row-wise softmax in a single streaming pass, avoiding the need to materialize the full N x N attention matrix. This is the key algorithmic innovation behind FlashAttention.

### **87.2.1 SoftmaxState**
The state tracks two running statistics: the maximum value seen so far and the sum of exponentials relative to that maximum.

```cpp
// online_softmax.cuh - Incremental softmax state
struct SoftmaxState {
    float max_val;  // Running maximum
    float sum_exp;  // Running sum of exp(x - max)
};
```

### **87.2.2 Update and Merge**
New values are incorporated via `online_softmax_update`, which adjusts the running sum when a new maximum is encountered. Two partial states from different tile iterations can be combined via `online_softmax_merge` for parallel reduction.

```cpp
// online_softmax.cuh - Streaming update
__device__ void online_softmax_update(SoftmaxState& state, float val) {
    float new_max = fmaxf(state.max_val, val);
    float exp_diff = expf(state.max_val - new_max);
    state.sum_exp = state.sum_exp * exp_diff + expf(val - new_max);
    state.max_val = new_max;
}
```
**Key Points**:
- Numerically stable: works correctly with values in the range [-500, +500]
- Single-pass: no need to store all values before computing softmax
- Mergeable: supports parallel reduction across warps/blocks

**Source**: `src/common/online_softmax.cuh`

### **87.2.3 Rescale for FlashAttention**
When processing a new key tile changes the running maximum, previously accumulated output (partial P*V products) must be rescaled. The `online_softmax_rescale` function handles this correction.

```cpp
// online_softmax.cuh - Rescale accumulated output
__device__ float online_softmax_rescale(
    float old_val, float old_max, float new_max, float old_sum, float new_sum) {
    return old_val * (expf(old_max - new_max) * old_sum / new_sum);
}
```

---

## **87.3 Causal Masking**
Causal masking enforces the autoregressive property: each query position can only attend to itself and earlier key positions. This creates a lower-triangular attention pattern.

### **87.3.1 Element-Level Predicates**
The basic `causal_keep` predicate checks whether a single (q, k) position should be attended to. The `apply_causal_mask` function returns either the original score or negative infinity.

```cpp
// causal_mask.cuh - Lower-triangular mask
__device__ bool causal_keep(int q, int k) { return k <= q; }
__device__ float apply_causal_mask(float score, int q, int k) {
    return causal_keep(q, k) ? score : -FLT_MAX;
}
```

**Source**: `src/common/causal_mask.cuh`

### **87.3.2 Tile-Level Optimizations**
For tiled attention, entire tiles can sometimes be classified as fully masked or fully unmasked, avoiding per-element predicate evaluation.

```cpp
// causal_mask.cuh - Skip entire tiles
__device__ bool tile_fully_masked(int q_start, int q_size, int k_start) {
    return k_start > (q_start + q_size - 1);
}
__device__ bool tile_fully_unmasked(int q_start, int k_start, int k_size) {
    return q_start >= (k_start + k_size - 1);
}
```
**Key Points**:
- `tile_fully_masked`: key tile starts after all query positions -- skip the entire GEMM
- `tile_fully_unmasked`: key tile ends before the first query position -- no per-element masking needed
- Diagonal tiles require per-element `tile_causal_keep` checks

---

## **87.4 QKV Packing**
Multi-head attention requires converting between the natural token-interleaved layout `[B,T,H,D]` and the head-grouped computation layout `[B,H,T,D]`. The head-grouped layout enables efficient batched GEMM across heads.

### **87.4.1 Layout Reordering Kernels**
Each thread handles one element, computing source and destination indices from the flat thread index.

```cpp
// qkv_packing.cuh - [B,T,H,D] -> [B,H,T,D]
__global__ void bthd_to_bhtd(float* output, const float* input,
                              int B, int T, int H, int D) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    // decompose idx -> (b, t, h, d), compute src/dst indices
}
```
**Source**: `src/common/qkv_packing.cuh`

### **87.4.2 Host Launch Wrappers**
Convenience functions that compute grid/block dimensions and launch the kernels.

```cpp
// qkv_packing.cuh - Host launcher
void reorder_bthd_to_bhtd(float* output, const float* input,
                            int B, int T, int H, int D, cudaStream_t stream = 0);
void reorder_bhtd_to_bthd(float* output, const float* input,
                            int B, int T, int H, int D, cudaStream_t stream = 0);
```
**Key Points**:
- Roundtrip `BTHD -> BHTD -> BTHD` preserves data exactly
- With `H=1` or `T=1`, the reorder is an identity transform
- Block size is 256 threads; grid is sized to cover `B*T*H*D` elements

---

## **87.5 Summary**
- **Key Takeaways**:
  - `SDPATileConfig` encapsulates tile dimensions for architecture-aware SDPA blocking
  - Online softmax enables single-pass numerically stable softmax without materializing the full attention matrix
  - Causal mask predicates support both element-level and tile-level fast-path evaluation
  - QKV packing kernels convert between natural and computation tensor layouts for multi-head attention
- **Common Errors**:

  | Error | Cause | Solution |
  |-------|-------|----------|
  | NaN in softmax output | Overflow in naive `exp()` | Use online softmax with running max subtraction |
  | Wrong attention pattern | Mask predicate direction reversed | Ensure `k <= q` (not `q <= k`) for causal |
  | Incorrect head outputs | Wrong layout after reorder | Verify roundtrip `BTHD->BHTD->BTHD` preserves data |
  | Shared memory overflow | Tile too large for architecture | Use `sdpa_smem_size()` to check before launch |

- **Next Steps**: [82.Attention_Kernels](../82.Attention_Kernels/README.md) -- FlashAttention implementation that consumes these primitives
- **References**: [FlashAttention paper](https://arxiv.org/abs/2205.14135), [Online Softmax (Milakov & Gimelshein 2018)](https://arxiv.org/abs/1805.02867)

---

## Build & Run

```bash
# From build directory
cmake --build . --target 87_Attention_Common_API_lib
cmake --build . --target 87_Attention_Common_API_test
./80.Transformer/87.Attention_Common_API/87_Attention_Common_API_test

# Generate documentation
ninja doxygen_87_Attention_Common_API
```
