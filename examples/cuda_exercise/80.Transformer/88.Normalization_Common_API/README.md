# Part 88: Normalization Common API
**Goal**: Provide reusable warp-level and block-level reduction primitives, plus mean/variance/RMS helpers, that serve as the computational foundation for LayerNorm and RMSNorm kernels.

## Project Structure
```
88.Normalization_Common_API/
├── CMakeLists.txt
├── README.md
├── doxygen/
│   ├── Doxyfile.in
│   └── mainpage.md
├── src/
│   ├── CMakeLists.txt
│   └── common/
│       ├── reduce_warp.cuh       # Warp-level reductions (sum, max, min)
│       ├── reduce_warp.cu
│       ├── reduce_block.cuh      # Block-level reductions via shared memory
│       ├── reduce_block.cu
│       ├── mean_rsqrt.cuh        # Mean, variance, and RMS helpers
│       └── mean_rsqrt.cu
└── test/
    ├── CMakeLists.txt
    └── unit/
        └── kernels/
            ├── test_reduce_warp.cu
            ├── test_reduce_block.cu
            └── test_mean_rsqrt.cu
```

## Quick Navigation
- [88.1 Warp-Level Reduction](#881-warp-level-reduction)
- [88.2 Block-Level Reduction](#882-block-level-reduction)
- [88.3 Mean and RMS](#883-mean-and-rms)
- [88.4 Summary](#884-summary)
- [Build & Run](#build--run)

---

## **88.1 Warp-Level Reduction**
Warp-level reductions are the fastest parallel reduction primitives on NVIDIA GPUs because they use register-to-register shuffle instructions (`__shfl_xor_sync`) with no shared memory overhead.

### **88.1.1 Butterfly Shuffle Pattern**
The butterfly pattern performs log2(32) = 5 rounds of XOR-based shuffles, halving the communication distance each round (16, 8, 4, 2, 1). After all rounds, every lane holds the fully reduced value.

```cpp
// reduce_warp.cuh - Warp-level sum via butterfly shuffle
__device__ __forceinline__ float warp_reduce_sum(float val) {
    for (int offset = 16; offset > 0; offset >>= 1) {
        val += __shfl_xor_sync(0xffffffff, val, offset);
    }
    return val;
}
```

**Key Points**:
- All 32 lanes participate with a full mask (`0xffffffff`)
- Result is broadcast to every lane (no need for lane-0-only reads)
- Zero shared memory usage -- entirely register-based
- Works for sum, max, and min by swapping the reduction operator

**Source**: `src/common/reduce_warp.cuh`

### **88.1.2 Supported Operations**
Three core reduction operations are provided, each using the same butterfly pattern.

| Function | Operator | Identity |
|---|---|---|
| `warp_reduce_sum` | `+` | `0.0f` |
| `warp_reduce_max` | `fmaxf` | `-FLT_MAX` |
| `warp_reduce_min` | `fminf` | `FLT_MAX` |

### **88.1.3 Partial Warp Reduction**
When fewer than 32 threads are active (e.g., tail elements), `warp_reduce_sum_partial` accepts an `active_lanes` count and computes a reduced mask to avoid reading from inactive lanes.

```cpp
// reduce_warp.cuh - Partial warp sum
template<int WARP_SIZE = 32>
__device__ __forceinline__ float warp_reduce_sum_partial(float val, int active_lanes) {
    unsigned mask = (active_lanes >= 32) ? 0xffffffff : ((1u << active_lanes) - 1);
    for (int offset = 16; offset > 0; offset >>= 1) {
        val += __shfl_xor_sync(mask, val, offset);
    }
    return val;
}
```

---

## **88.2 Block-Level Reduction**
Block-level reductions extend warp reductions to work across an entire thread block (up to 1024 threads / 32 warps) by introducing a shared memory communication step between warps.

### **88.2.1 Two-Phase Algorithm**
The block reduction proceeds in two phases.

**Phase 1 -- Intra-warp**: Each warp independently reduces its 32 values using `warp_reduce_sum`. Lane 0 of each warp writes its partial result to shared memory.

**Phase 2 -- Inter-warp**: Warp 0 reads all partial results from shared memory and performs a final warp-level reduction. The result is written back to `smem[0]` and broadcast to all threads via a `__syncthreads()` barrier.

```cpp
// reduce_block.cuh - Block-level sum reduction
__device__ __forceinline__ float block_reduce_sum(float val, float* smem) {
    int lane = threadIdx.x % 32;
    int warp_id = threadIdx.x / 32;
    int num_warps = (blockDim.x + 31) / 32;

    val = warp_reduce_sum(val);           // Phase 1: intra-warp
    if (lane == 0) smem[warp_id] = val;
    __syncthreads();

    if (warp_id == 0) {                   // Phase 2: inter-warp
        val = (lane < num_warps) ? smem[lane] : 0.0f;
        val = warp_reduce_sum(val);
    }
    __syncthreads();
    if (threadIdx.x == 0) smem[0] = val;  // Broadcast
    __syncthreads();
    return smem[0];
}
```

**Key Points**:
- Shared memory requirement: `ceil(blockDim.x / 32) * sizeof(float)` bytes
- Three `__syncthreads()` barriers guarantee correctness
- Result is broadcast to all threads, not just thread 0
- Supports up to 1024 threads (32 warps, which fits within a single warp for phase 2)

**Source**: `src/common/reduce_block.cuh`

### **88.2.2 Block Max Reduction**
The max variant follows the same two-phase pattern but uses `warp_reduce_max` and initializes inactive lanes to `-FLT_MAX` instead of `0.0f`.

---

## **88.3 Mean and RMS**
Higher-level helpers combine strided data loading with block reductions to compute statistics needed by LayerNorm and RMSNorm.

### **88.3.1 Mean Computation**
Each thread accumulates elements from a row in a grid-stride loop, then the block reduces the partial sums and divides by `n`.

```cpp
// mean_rsqrt.cuh
__device__ __forceinline__ float compute_mean(const float* input, int n, float* smem) {
    float sum = 0.0f;
    for (int i = threadIdx.x; i < n; i += blockDim.x) {
        sum += input[i];
    }
    sum = block_reduce_sum(sum, smem);
    return sum / static_cast<float>(n);
}
```

**Source**: `src/common/mean_rsqrt.cuh`

### **88.3.2 Variance Computation**
Given a pre-computed mean, each thread accumulates squared differences in a stride loop, then the block reduces to produce the population variance.

```cpp
// mean_rsqrt.cuh
__device__ __forceinline__ float compute_variance(const float* input, float mean, int n, float* smem) {
    float sum_sq = 0.0f;
    for (int i = threadIdx.x; i < n; i += blockDim.x) {
        float diff = input[i] - mean;
        sum_sq += diff * diff;
    }
    sum_sq = block_reduce_sum(sum_sq, smem);
    return sum_sq / static_cast<float>(n);
}
```

### **88.3.3 RMS Reciprocal Square Root**
Used by RMSNorm, this computes `rsqrt(mean(x^2) + eps)` in a single pass.

```cpp
// mean_rsqrt.cuh
__device__ __forceinline__ float compute_rms_rsqrt(const float* input, int n, float eps, float* smem) {
    float sum_sq = 0.0f;
    for (int i = threadIdx.x; i < n; i += blockDim.x) {
        sum_sq += input[i] * input[i];
    }
    sum_sq = block_reduce_sum(sum_sq, smem);
    float rms = sum_sq / static_cast<float>(n);
    return rsqrtf(rms + eps);
}
```

**Key Points**:
- Single pass over data (no separate mean computation needed for RMSNorm)
- `eps` prevents division by zero when inputs are near zero
- `rsqrtf` is a hardware-accelerated instruction on NVIDIA GPUs

---

## **88.4 Summary**

- **Key Takeaways**:
  - Warp shuffles provide the fastest intra-warp reductions with zero shared memory cost
  - Block reductions compose warp reductions via a shared memory inter-warp step
  - Mean, variance, and RMS helpers combine strided loading with block reductions for normalization
  - All functions broadcast results to every thread in the block
  - The `transformer` namespace keeps these primitives isolated from other modules

- **Performance Characteristics**:
  - Warp reduction: 5 shuffle instructions (log2(32)), ~10 cycles
  - Block reduction: 5 shuffles + 3 syncthreads + shared memory read/write
  - Mean/variance: dominated by global memory bandwidth for the stride loop

- **Common Errors**:

  | Error | Cause | Solution |
  |---|---|---|
  | Incorrect reduction with non-power-of-2 threads | Inactive lanes contribute garbage | Use `warp_reduce_sum_partial` or pad to warp boundary |
  | Shared memory not allocated | Missing `extern __shared__` or insufficient dynamic shmem | Pass `ceil(blockDim.x/32)*sizeof(float)` as shmem arg |
  | Race condition in block reduction | Missing `__syncthreads()` | Ensure all three barriers are present |

- **Next Steps**: [84.Normalization](../84.Normalization/README.md) -- uses these primitives to implement full LayerNorm and RMSNorm kernels

- **References**:
  - [CUDA Warp Shuffle Functions](https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#warp-shuffle-functions)
  - [CUDA Shared Memory](https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#shared-memory)

---

## Build & Run

```bash
# From the repository build directory
cmake --build . --target 88_Normalization_Common_API_test
ctest -R 88_Normalization_Common_API

# Generate documentation
ninja doxygen_88_Normalization_Common_API
```
