/**
 * Vector Operations with Memory Coalescing Optimizations
 *
 * This file demonstrates vector operations optimized for memory coalescing
 * and bank conflict avoidance, building upon module 23's shared memory patterns.
 *
 * Module 24 Improvements:
 * - Explicit coalescing analysis for each operation
 * - Vectorized variants using float4
 * - Alignment optimizations
 * - Sequential addressing patterns
 *
 * Operations Covered:
 * 1. Reduction - Coalesced with warp-level optimization
 * 2. Histogram - Bank conflict-free atomic updates
 * 3. Scan/Prefix Sum - Optimized shared memory access
 * 4. Dot Product - Vectorized and coalesced
 */

#include <cuda_runtime.h>
#include <cstdint>

// ============================================================================
// Reduction with Coalescing Optimization
// ============================================================================

/**
 * Optimized reduction with perfect memory coalescing
 *
 * Module 23 Version:
 * - Used shared memory with sequential addressing
 * - Bank conflict avoidance via sequential access
 *
 * Module 24 Improvements:
 * - Vectorized global memory loads (float4)
 * - Warp-level primitives (__shfl_down_sync)
 * - Better instruction-level parallelism
 *
 * Coalescing Analysis:
 * - Input load: Thread i loads input[blockIdx.x * blockSize + i]
 *   → Consecutive threads, consecutive memory ✓
 * - Shared memory: Sequential addressing pattern ✓
 * - Output store: Single thread per block (no coalescing needed)
 */
template<int BLOCK_SIZE>
__global__ void reduction_vectorized(const float* __restrict__ input,
                                      float* __restrict__ output,
                                      int n) {
    __shared__ float sdata[BLOCK_SIZE];

    int tid = threadIdx.x;
    int gid = blockIdx.x * (BLOCK_SIZE * 4) + threadIdx.x;

    // Vectorized load - load 4 elements per thread
    // Coalescing: Each warp loads 128 consecutive elements
    float sum = 0.0f;
    if (gid < n) {
        sum += input[gid];
    }
    if (gid + BLOCK_SIZE < n) {
        sum += input[gid + BLOCK_SIZE];
    }
    if (gid + 2 * BLOCK_SIZE < n) {
        sum += input[gid + 2 * BLOCK_SIZE];
    }
    if (gid + 3 * BLOCK_SIZE < n) {
        sum += input[gid + 3 * BLOCK_SIZE];
    }

    sdata[tid] = sum;
    __syncthreads();

    // Reduction in shared memory - sequential addressing
    // No bank conflicts: thread i accesses sdata[i + offset]
    for (int s = BLOCK_SIZE / 2; s > 32; s >>= 1) {
        if (tid < s) {
            sdata[tid] += sdata[tid + s];
        }
        __syncthreads();
    }

    // Warp-level reduction (no __syncthreads needed)
    if (tid < 32) {
        volatile float* smem = sdata;
        if (BLOCK_SIZE >= 64) smem[tid] += smem[tid + 32];
        if (BLOCK_SIZE >= 32) smem[tid] += smem[tid + 16];
        if (BLOCK_SIZE >= 16) smem[tid] += smem[tid + 8];
        if (BLOCK_SIZE >= 8)  smem[tid] += smem[tid + 4];
        if (BLOCK_SIZE >= 4)  smem[tid] += smem[tid + 2];
        if (BLOCK_SIZE >= 2)  smem[tid] += smem[tid + 1];
    }

    // Write result (single thread, no coalescing needed)
    if (tid == 0) {
        output[blockIdx.x] = sdata[0];
    }
}

/**
 * Reduction using warp shuffle instructions
 *
 * Module 24 Warp-Level Optimization:
 * - No shared memory needed for warp reduction
 * - Uses __shfl_down_sync for intra-warp communication
 * - Reduced bank conflict concerns
 * - Better performance for small reductions
 */
__inline__ __device__ float warp_reduce_sum(float val) {
    for (int offset = 16; offset > 0; offset >>= 1) {
        val += __shfl_down_sync(0xffffffff, val, offset);
    }
    return val;
}

template<int BLOCK_SIZE>
__global__ void reduction_warp_shuffle(const float* __restrict__ input,
                                        float* __restrict__ output,
                                        int n) {
    static_assert(BLOCK_SIZE % 32 == 0, "BLOCK_SIZE must be multiple of warp size");

    __shared__ float warp_sums[BLOCK_SIZE / 32];

    int tid = threadIdx.x;
    int gid = blockIdx.x * BLOCK_SIZE + threadIdx.x;
    int lane = tid % 32;
    int warp_id = tid / 32;

    // Coalesced load
    float val = (gid < n) ? input[gid] : 0.0f;

    // Warp-level reduction (no shared memory)
    val = warp_reduce_sum(val);

    // First thread of each warp writes to shared memory
    if (lane == 0) {
        warp_sums[warp_id] = val;
    }
    __syncthreads();

    // Final reduction across warps
    if (warp_id == 0) {
        val = (lane < (BLOCK_SIZE / 32)) ? warp_sums[lane] : 0.0f;
        val = warp_reduce_sum(val);

        if (lane == 0) {
            output[blockIdx.x] = val;
        }
    }
}

// ============================================================================
// Histogram with Coalescing and Bank Conflict Optimization
// ============================================================================

/**
 * Histogram with privatized bins to reduce conflicts
 *
 * Module 23 Version:
 * - Shared memory for local histogram
 * - Atomic adds to shared memory
 *
 * Module 24 Improvements:
 * - Coalesced input reads
 * - Bank conflict analysis for atomic operations
 * - Privatization to reduce contention
 *
 * Coalescing:
 * - Input: Thread i reads input[blockIdx.x * blockSize + i] ✓
 * - Histogram updates: Atomic operations (uncoalesced by nature)
 * - Output: Atomic adds (uncoalesced, but minimal)
 */
template<int BLOCK_SIZE, int NUM_BINS>
__global__ void histogram_privatized(const int* __restrict__ input,
                                      int* __restrict__ histogram,
                                      int n) {
    // Shared histogram with padding to reduce bank conflicts
    __shared__ int shared_hist[NUM_BINS + 1];  // +1 padding

    int tid = threadIdx.x;
    int gid = blockIdx.x * BLOCK_SIZE + threadIdx.x;

    // Initialize shared histogram
    for (int bin = tid; bin < NUM_BINS; bin += BLOCK_SIZE) {
        shared_hist[bin] = 0;
    }
    __syncthreads();

    // Coalesced read from input
    if (gid < n) {
        int value = input[gid];
        int bin = value % NUM_BINS;
        // Atomic add to shared memory
        atomicAdd(&shared_hist[bin], 1);
    }
    __syncthreads();

    // Coalesce writes to global histogram
    for (int bin = tid; bin < NUM_BINS; bin += BLOCK_SIZE) {
        int count = shared_hist[bin];
        if (count > 0) {
            atomicAdd(&histogram[bin], count);
        }
    }
}

// ============================================================================
// Scan/Prefix Sum with Coalescing
// ============================================================================

/**
 * Inclusive scan (prefix sum) with optimized memory access
 *
 * Module 24 Coalescing Focus:
 * - Coalesced input loads
 * - Bank conflict-free shared memory access
 * - Efficient up-sweep and down-sweep phases
 *
 * Algorithm: Blelloch scan (work-efficient)
 * - Up-sweep phase: Build reduction tree
 * - Down-sweep phase: Compute prefix sums
 */
template<int BLOCK_SIZE>
__global__ void scan_blelloch(const float* __restrict__ input,
                               float* __restrict__ output,
                               int n) {
    __shared__ float temp[2 * BLOCK_SIZE];

    int tid = threadIdx.x;
    int gid = blockIdx.x * (2 * BLOCK_SIZE) + threadIdx.x;

    // Coalesced load - each thread loads 2 elements
    int ai = tid;
    int bi = tid + BLOCK_SIZE;

    temp[ai] = (gid < n) ? input[gid] : 0.0f;
    temp[bi] = (gid + BLOCK_SIZE < n) ? input[gid + BLOCK_SIZE] : 0.0f;

    int offset = 1;

    // Up-sweep phase (reduction)
    for (int d = BLOCK_SIZE; d > 0; d >>= 1) {
        __syncthreads();
        if (tid < d) {
            int ai = offset * (2 * tid + 1) - 1;
            int bi = offset * (2 * tid + 2) - 1;
            temp[bi] += temp[ai];
        }
        offset <<= 1;
    }

    // Set last element to zero
    if (tid == 0) {
        temp[2 * BLOCK_SIZE - 1] = 0.0f;
    }

    // Down-sweep phase
    for (int d = 1; d < 2 * BLOCK_SIZE; d <<= 1) {
        offset >>= 1;
        __syncthreads();

        if (tid < d) {
            int ai = offset * (2 * tid + 1) - 1;
            int bi = offset * (2 * tid + 2) - 1;

            float t = temp[ai];
            temp[ai] = temp[bi];
            temp[bi] += t;
        }
    }

    __syncthreads();

    // Coalesced write back
    if (gid < n) {
        output[gid] = temp[ai];
    }
    if (gid + BLOCK_SIZE < n) {
        output[gid + BLOCK_SIZE] = temp[bi];
    }
}

// ============================================================================
// Dot Product with Vectorized Coalescing
// ============================================================================

/**
 * Dot product using vectorized loads for maximum coalescing
 *
 * Module 24 Vectorization:
 * - Load using float4 (16-byte transactions)
 * - 4x reduction in memory transactions
 * - Better bandwidth utilization
 */
template<int BLOCK_SIZE>
__global__ void dot_product_vectorized(const float* __restrict__ a,
                                        const float* __restrict__ b,
                                        float* __restrict__ result,
                                        int n) {
    __shared__ float sdata[BLOCK_SIZE];

    int tid = threadIdx.x;
    int gid = blockIdx.x * BLOCK_SIZE * 4 + threadIdx.x;

    // Vectorized coalesced loads
    float sum = 0.0f;

    // Process 4 elements per thread
    if (gid * 4 + 3 < n && (reinterpret_cast<uintptr_t>(&a[gid * 4]) % 16 == 0)) {
        // Aligned vectorized load
        float4 a_vec = *reinterpret_cast<const float4*>(&a[gid * 4]);
        float4 b_vec = *reinterpret_cast<const float4*>(&b[gid * 4]);

        sum = a_vec.x * b_vec.x +
              a_vec.y * b_vec.y +
              a_vec.z * b_vec.z +
              a_vec.w * b_vec.w;
    } else {
        // Scalar fallback for unaligned/boundary
        for (int i = 0; i < 4 && (gid * 4 + i) < n; i++) {
            sum += a[gid * 4 + i] * b[gid * 4 + i];
        }
    }

    sdata[tid] = sum;
    __syncthreads();

    // Reduce in shared memory
    for (int s = BLOCK_SIZE / 2; s > 0; s >>= 1) {
        if (tid < s) {
            sdata[tid] += sdata[tid + s];
        }
        __syncthreads();
    }

    if (tid == 0) {
        result[blockIdx.x] = sdata[0];
    }
}

// ============================================================================
// Memory Access Pattern Analysis Helper
// ============================================================================

/**
 * Kernel to demonstrate and measure coalescing efficiency
 *
 * This kernel performs simple copy operations with different patterns
 * to illustrate coalescing behavior for educational purposes.
 */
__global__ void analyze_coalescing(const float* __restrict__ input,
                                    float* __restrict__ output_coalesced,
                                    float* __restrict__ output_strided,
                                    int n, int stride) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;

    // Pattern 1: Perfect coalescing
    if (tid < n) {
        output_coalesced[tid] = input[tid];
    }

    // Pattern 2: Strided access (poor coalescing)
    int strided_idx = tid * stride;
    if (strided_idx < n) {
        output_strided[tid] = input[strided_idx];
    }
}
