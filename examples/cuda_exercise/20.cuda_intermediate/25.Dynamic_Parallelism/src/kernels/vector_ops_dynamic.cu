/**
 * Vector Operations with Dynamic Parallelism
 *
 * This file enhances Module 24's vector operations by adding dynamic
 * parallelism for adaptive workload distribution and recursive algorithms.
 *
 * Dynamic Parallelism Features:
 * 1. Recursive Reduction - Multi-level reduction with dynamic kernel launches
 * 2. Adaptive Histogram - Dynamic binning with child kernel spawning
 * 3. Dynamic Scan - Recursive prefix sum computation
 * 4. Hierarchical Processing - Parent-child workload distribution
 *
 * Module 25 Focus: Dynamic kernel launches for vector operations
 */

#include <cuda_runtime.h>
#include <cuda_device_runtime_api.h>
#include <cstdint>

// Maximum recursion depth
#define MAX_REDUCTION_DEPTH 4

// Threshold for launching child kernels
#define RECURSIVE_THRESHOLD 1024

// ============================================================================
// Base Reduction Kernel (Leaf Computation)
// ============================================================================

/**
 * Optimized reduction kernel (leaf-level computation)
 * Used as the base case for recursive reduction
 */
template<int BLOCK_SIZE>
__global__ void reduction_leaf(const float* __restrict__ input,
                                float* __restrict__ output,
                                int n, int offset) {
    __shared__ float sdata[BLOCK_SIZE];

    int tid = threadIdx.x;
    int gid = offset + blockIdx.x * (BLOCK_SIZE * 4) + threadIdx.x;
    int end = offset + n;

    // Vectorized load - 4 elements per thread
    float sum = 0.0f;
    if (gid < end) sum += input[gid];
    if (gid + BLOCK_SIZE < end) sum += input[gid + BLOCK_SIZE];
    if (gid + 2 * BLOCK_SIZE < end) sum += input[gid + 2 * BLOCK_SIZE];
    if (gid + 3 * BLOCK_SIZE < end) sum += input[gid + 3 * BLOCK_SIZE];

    sdata[tid] = sum;
    __syncthreads();

    // Reduction in shared memory
    for (int s = BLOCK_SIZE / 2; s > 32; s >>= 1) {
        if (tid < s) {
            sdata[tid] += sdata[tid + s];
        }
        __syncthreads();
    }

    // Warp-level reduction (use explicit sync instead of deprecated volatile)
    if (tid < 32) {
        if (BLOCK_SIZE >= 64) { sdata[tid] += sdata[tid + 32]; __syncwarp(); }
        if (BLOCK_SIZE >= 32) { sdata[tid] += sdata[tid + 16]; __syncwarp(); }
        if (BLOCK_SIZE >= 16) { sdata[tid] += sdata[tid + 8];  __syncwarp(); }
        if (BLOCK_SIZE >= 8)  { sdata[tid] += sdata[tid + 4];  __syncwarp(); }
        if (BLOCK_SIZE >= 4)  { sdata[tid] += sdata[tid + 2];  __syncwarp(); }
        if (BLOCK_SIZE >= 2)  { sdata[tid] += sdata[tid + 1];  __syncwarp(); }
    }

    if (tid == 0) {
        output[blockIdx.x] = sdata[0];
    }
}

// ============================================================================
// Dynamic Parallelism: Recursive Reduction
// ============================================================================

/**
 * Recursive reduction with dynamic parallelism
 *
 * Strategy:
 * - Level 0: Reduce large array to block-level results
 * - Level 1+: Parent kernel launches child to reduce block results
 * - Continues recursively until single value remains
 *
 * Advantages:
 * - No CPU involvement after initial launch
 * - Adapts to problem size dynamically
 * - Efficient for very large arrays
 */
template<int BLOCK_SIZE>
__global__ void reduction_recursive(float* data, float* temp, int n, int depth) {
    // Only first thread in first block manages recursion
    if (threadIdx.x != 0 || blockIdx.x != 0) {
        return;
    }

    // Base case: array small enough for single block
    if (n <= BLOCK_SIZE * 4 || depth >= MAX_REDUCTION_DEPTH) {
        reduction_leaf<BLOCK_SIZE><<<1, BLOCK_SIZE>>>(data, data, n, 0);
        return;
    }

    // Recursive case: launch grid of blocks
    int blocks = (n + (BLOCK_SIZE * 4) - 1) / (BLOCK_SIZE * 4);

    // First level reduction: data -> temp
    reduction_leaf<BLOCK_SIZE><<<blocks, BLOCK_SIZE>>>(data, temp, n, 0);

    // Recursive reduction on block results
    reduction_recursive<BLOCK_SIZE><<<1, 1>>>(temp, temp + blocks, blocks, depth + 1);

    // Final result is in temp[0]
    if (depth == 0) {
        data[0] = temp[0];
    }
}

// ============================================================================
// Dynamic Parallelism: Segmented Reduction
// ============================================================================

/**
 * Reduction of multiple segments with dynamic parallelism
 *
 * Each segment can be reduced independently.
 * Parent kernel analyzes segments and launches children accordingly.
 */
template<int BLOCK_SIZE>
__global__ void reduction_segmented_parent(const float* input,
                                            float* output,
                                            const int* segment_sizes,
                                            const int* segment_offsets,
                                            int num_segments) {
    int seg_id = blockIdx.x * blockDim.x + threadIdx.x;

    if (seg_id < num_segments) {
        int offset = segment_offsets[seg_id];
        int size = segment_sizes[seg_id];

        // All segments are small (size <= BLOCK_SIZE * 4), so single block
        // Launch child kernel for this segment
        reduction_leaf<BLOCK_SIZE><<<1, BLOCK_SIZE>>>(
            input, output + seg_id, size, offset);
    }
}

// ============================================================================
// Dynamic Parallelism: Adaptive Histogram
// ============================================================================

/**
 * Child kernel for computing histogram of a range
 */
__global__ void histogram_range_kernel(const int* data,
                                        int* histogram,
                                        int start, int end,
                                        int num_bins) {
    int idx = start + blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < end) {
        int bin = data[idx] % num_bins;
        atomicAdd(&histogram[bin], 1);
    }
}

/**
 * Adaptive histogram with dynamic work distribution
 *
 * Parent kernel divides data into chunks and launches
 * child kernels based on chunk size and characteristics.
 */
__global__ void histogram_adaptive_dynamic(const int* data,
                                            int* histogram,
                                            int n,
                                            int num_bins,
                                            int chunks) {
    int chunk_id = blockIdx.x * blockDim.x + threadIdx.x;

    if (chunk_id < chunks) {
        int chunk_size = (n + chunks - 1) / chunks;
        int start = chunk_id * chunk_size;
        int end = min(start + chunk_size, n);

        if (start < end) {
            // Launch child kernel for this chunk
            int threads = 256;
            int blocks = (end - start + threads - 1) / threads;

            histogram_range_kernel<<<blocks, threads>>>(
                data, histogram, start, end, num_bins);
        }
    }
}

// ============================================================================
// Dynamic Parallelism: Hierarchical Scan (Prefix Sum)
// ============================================================================

/**
 * Single-block scan kernel (base case)
 */
template<int BLOCK_SIZE>
__global__ void scan_block(const float* input,
                            float* output,
                            float* block_sums,
                            int n,
                            int offset) {
    __shared__ float temp[BLOCK_SIZE * 2];

    int tid = threadIdx.x;
    int gid = offset + blockIdx.x * BLOCK_SIZE + tid;

    // Load data
    temp[tid] = (gid < n) ? input[gid] : 0.0f;
    __syncthreads();

    // Up-sweep (reduce) phase
    int d;
    for (d = 1; d < BLOCK_SIZE; d *= 2) {
        int idx = (tid + 1) * 2 * d - 1;
        if (idx < BLOCK_SIZE) {
            temp[idx] += temp[idx - d];
        }
        __syncthreads();
    }

    // Save block sum
    if (tid == 0) {
        if (block_sums != nullptr) {
            block_sums[blockIdx.x] = temp[BLOCK_SIZE - 1];
        }
        temp[BLOCK_SIZE - 1] = 0;
    }
    __syncthreads();

    // Down-sweep phase
    for (d = BLOCK_SIZE / 2; d > 0; d /= 2) {
        int idx = (tid + 1) * 2 * d - 1;
        if (idx < BLOCK_SIZE) {
            float t = temp[idx - d];
            temp[idx - d] = temp[idx];
            temp[idx] += t;
        }
        __syncthreads();
    }

    // Write output
    if (gid < n) {
        output[gid] = temp[tid];
    }
}

/**
 * Recursive hierarchical scan with dynamic parallelism
 *
 * Strategy:
 * 1. Each block computes local scan and outputs block sum
 * 2. Parent recursively scans block sums
 * 3. Add scanned block sums back to each block's results
 */
template<int BLOCK_SIZE>
__global__ void scan_recursive(float* data,
                                float* temp,
                                int n,
                                int depth) {
    if (threadIdx.x != 0 || blockIdx.x != 0) return;

    // Base case
    if (n <= BLOCK_SIZE || depth >= MAX_REDUCTION_DEPTH) {
        scan_block<BLOCK_SIZE><<<1, BLOCK_SIZE>>>(data, data, nullptr, n, 0);
        return;
    }

    // Recursive case
    int blocks = (n + BLOCK_SIZE - 1) / BLOCK_SIZE;

    // Level 1: Scan each block, output block sums
    scan_block<BLOCK_SIZE><<<blocks, BLOCK_SIZE>>>(data, data, temp, n, 0);

    // Level 2: Recursively scan block sums
    scan_recursive<BLOCK_SIZE><<<1, 1>>>(temp, temp + blocks, blocks, depth + 1);

    // Note: Would need to add scanned sums back to each block's data
    // Simplified here for demonstration
}

// ============================================================================
// Dynamic Parallelism: Adaptive Dot Product
// ============================================================================

/**
 * Dot product child kernel for computing partial products
 */
template<int BLOCK_SIZE>
__global__ void dot_product_partial(const float* a,
                                     const float* b,
                                     float* partial_sums,
                                     int start, int end) {
    __shared__ float sdata[BLOCK_SIZE];

    int tid = threadIdx.x;
    int gid = start + blockIdx.x * BLOCK_SIZE + tid;

    float sum = 0.0f;
    if (gid < end) {
        sum = a[gid] * b[gid];
    }

    sdata[tid] = sum;
    __syncthreads();

    // Reduce within block
    for (int s = BLOCK_SIZE / 2; s > 0; s >>= 1) {
        if (tid < s) {
            sdata[tid] += sdata[tid + s];
        }
        __syncthreads();
    }

    if (tid == 0) {
        partial_sums[blockIdx.x] = sdata[0];
    }
}

/**
 * Adaptive dot product with dynamic parallelism
 *
 * Parent decides optimal strategy based on vector size
 */
template<int BLOCK_SIZE>
__global__ void dot_product_adaptive(const float* a,
                                      const float* b,
                                      float* result,
                                      float* temp,
                                      int n) {
    if (threadIdx.x != 0 || blockIdx.x != 0) return;

    if (n <= BLOCK_SIZE) {
        // Small: single block
        dot_product_partial<BLOCK_SIZE><<<1, BLOCK_SIZE>>>(a, b, result, 0, n);
    } else {
        // Large: multiple blocks + recursive reduction
        int blocks = (n + BLOCK_SIZE - 1) / BLOCK_SIZE;

        // Compute partial sums
        dot_product_partial<BLOCK_SIZE><<<blocks, BLOCK_SIZE>>>(a, b, temp, 0, n);

        // Reduce partial sums
        reduction_recursive<BLOCK_SIZE><<<1, 1>>>(temp, temp + blocks, blocks, 0);

        result[0] = temp[0];
    }
}
