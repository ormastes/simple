/**
 * Advanced Cooperative Groups Patterns (Module 23 + Module 25 Enhanced)
 *
 * This file enhances Module 25's dynamic parallelism patterns with
 * cooperative groups for better synchronization and composability.
 *
 * Patterns Covered:
 * 1. Quicksort with cooperative groups
 * 2. Histogram with warp-level aggregation
 * 3. Matrix operations with tiled groups
 * 4. Scan (prefix sum) with cooperative collectives
 *
 * Improvements over Module 25 Dynamic Parallelism:
 * - No dynamic kernel launches (better performance)
 * - Warp-level intrinsics for efficiency
 * - Flexible synchronization domains
 * - Better composability
 */

#include <cuda_runtime.h>
#include <cooperative_groups.h>
#include <cooperative_groups/reduce.h>
#include <cstdint>

namespace cg = cooperative_groups;

// ============================================================================
// Cooperative Groups: Quicksort (Bitonic Sort)
// ============================================================================

/**
 * Bitonic sort using cooperative groups (replacement for recursive quicksort)
 *
 * Bitonic sort is data-parallel and avoids recursion.
 * Uses thread blocks and warps for efficient sorting.
 */
template<int BLOCK_SIZE>
__global__ void bitonic_sort_cg(int* data, int n) {
    cg::thread_block block = cg::this_thread_block();
    cg::thread_block_tile<32> warp = cg::tiled_partition<32>(block);

    __shared__ int sdata[BLOCK_SIZE];

    int tid = block.thread_rank();
    int gid = blockIdx.x * BLOCK_SIZE + tid;

    // Load data into shared memory
    sdata[tid] = (gid < n) ? data[gid] : INT_MAX;
    block.sync();

    // Bitonic sort in shared memory
    for (int k = 2; k <= BLOCK_SIZE; k *= 2) {
        // Bitonic merge
        for (int j = k / 2; j > 0; j /= 2) {
            int ixj = tid ^ j;

            if (ixj > tid) {
                // Determine sort direction
                bool ascending = ((tid & k) == 0);

                if ((sdata[tid] > sdata[ixj]) == ascending) {
                    // Swap using warp-level coordination
                    int temp = sdata[tid];
                    sdata[tid] = sdata[ixj];
                    sdata[ixj] = temp;
                }
            }

            block.sync();
        }
    }

    // Write sorted data back
    if (gid < n) {
        data[gid] = sdata[tid];
    }
}

// ============================================================================
// Cooperative Groups: Adaptive Histogram
// ============================================================================

/**
 * Warp-aggregated atomic histogram
 *
 * Uses warp-level reduction to aggregate bin updates before atomic operations.
 * This dramatically reduces atomic contention compared to Module 25's approach.
 */
template<int BLOCK_SIZE, int NUM_BINS>
__global__ void histogram_cg_warp_aggregated(const int* __restrict__ data,
                                               int* __restrict__ histogram,
                                               int n) {
    cg::thread_block block = cg::this_thread_block();
    cg::thread_block_tile<32> warp = cg::tiled_partition<32>(block);

    __shared__ int smem_hist[NUM_BINS];

    // Initialize shared histogram
    for (int i = threadIdx.x; i < NUM_BINS; i += BLOCK_SIZE) {
        smem_hist[i] = 0;
    }
    block.sync();

    // Process data with warp aggregation
    int gid = blockIdx.x * BLOCK_SIZE + threadIdx.x;

    if (gid < n) {
        int value = data[gid];
        int bin = value % NUM_BINS;

        // Warp-level aggregation:
        // Count how many threads in this warp want to update the same bin
        for (int i = 0; i < NUM_BINS; i++) {
            // Check if this thread targets bin i
            unsigned int mask = warp.ballot(bin == i);
            int leader = __ffs(mask) - 1;  // First thread targeting this bin

            if (mask != 0) {
                // Count threads targeting this bin
                int count = __popc(mask);

                // Designated leader performs one atomic instead of many
                if (warp.thread_rank() == leader) {
                    atomicAdd(&smem_hist[i], count);
                }
            }
        }
    }

    block.sync();

    // Merge to global histogram
    for (int i = threadIdx.x; i < NUM_BINS; i += BLOCK_SIZE) {
        if (smem_hist[i] > 0) {
            atomicAdd(&histogram[i], smem_hist[i]);
        }
    }
}

/**
 * Histogram with labeled partition (advanced technique)
 *
 * Uses cooperative groups to partition threads by their target bin.
 * Threads targeting the same bin form a group and coordinate.
 */
template<int BLOCK_SIZE>
__global__ void histogram_cg_labeled(const int* __restrict__ data,
                                      int* __restrict__ histogram,
                                      int n,
                                      int num_bins) {
    cg::thread_block block = cg::this_thread_block();

    __shared__ int smem_hist[256];  // Support up to 256 bins

    // Initialize
    if (threadIdx.x < num_bins) {
        smem_hist[threadIdx.x] = 0;
    }
    block.sync();

    int gid = blockIdx.x * BLOCK_SIZE + threadIdx.x;

    if (gid < n) {
        int value = data[gid];
        int bin = value % num_bins;

        // Create labeled partition - threads with same bin form a group
        cg::coalesced_group active = cg::coalesced_threads();

        // Within active threads, partition by bin value
        // Note: labeled_partition requires all threads to participate
        for (int target_bin = 0; target_bin < num_bins; target_bin++) {
            // Use ballot to find threads targeting this bin
            unsigned int mask = active.ballot(bin == target_bin);

            if (mask != 0) {
                int count = __popc(mask);
                int leader = __ffs(mask) - 1;

                // Leader updates histogram
                if (active.thread_rank() == leader) {
                    atomicAdd(&smem_hist[target_bin], count);
                }
            }
        }
    }

    block.sync();

    // Merge to global
    if (threadIdx.x < num_bins) {
        atomicAdd(&histogram[threadIdx.x], smem_hist[threadIdx.x]);
    }
}

// ============================================================================
// Cooperative Groups: Matrix Operations
// ============================================================================

/**
 * Matrix transpose using tiled cooperative groups
 *
 * Uses 2D thread block tiles for efficient transpose with no bank conflicts.
 */
template<int TILE_SIZE>
__global__ void matrix_transpose_cg(const float* __restrict__ input,
                                     float* __restrict__ output,
                                     int width,
                                     int height) {
    cg::thread_block block = cg::this_thread_block();

    // Padded shared memory to avoid bank conflicts
    __shared__ float tile[TILE_SIZE][TILE_SIZE + 1];

    int x = blockIdx.x * TILE_SIZE + threadIdx.x;
    int y = blockIdx.y * TILE_SIZE + threadIdx.y;

    // Cooperative load into shared memory
    if (x < width && y < height) {
        tile[threadIdx.y][threadIdx.x] = input[y * width + x];
    }

    block.sync();

    // Transposed coordinates
    x = blockIdx.y * TILE_SIZE + threadIdx.x;
    y = blockIdx.x * TILE_SIZE + threadIdx.y;

    // Cooperative write from shared memory (transposed)
    if (x < height && y < width) {
        output[y * height + x] = tile[threadIdx.x][threadIdx.y];
    }
}

/**
 * Matrix multiply using tiled cooperative groups
 *
 * Enhanced from Module 25 with explicit thread block tiles.
 */
template<int TILE_SIZE>
__global__ void matrix_multiply_cg(const float* __restrict__ A,
                                    const float* __restrict__ B,
                                    float* __restrict__ C,
                                    int M, int N, int K) {
    cg::thread_block block = cg::this_thread_block();

    __shared__ float As[TILE_SIZE][TILE_SIZE];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE];

    int bx = blockIdx.x;
    int by = blockIdx.y;
    int tx = threadIdx.x;
    int ty = threadIdx.y;

    int row = by * TILE_SIZE + ty;
    int col = bx * TILE_SIZE + tx;

    float sum = 0.0f;

    // Loop over tiles
    for (int m = 0; m < (K + TILE_SIZE - 1) / TILE_SIZE; m++) {
        // Collaborative tile loading
        if (row < M && m * TILE_SIZE + tx < K) {
            As[ty][tx] = A[row * K + m * TILE_SIZE + tx];
        } else {
            As[ty][tx] = 0.0f;
        }

        if (col < N && m * TILE_SIZE + ty < K) {
            Bs[ty][tx] = B[(m * TILE_SIZE + ty) * N + col];
        } else {
            Bs[ty][tx] = 0.0f;
        }

        block.sync();

        // Compute on tile
        #pragma unroll
        for (int k = 0; k < TILE_SIZE; k++) {
            sum += As[ty][k] * Bs[k][tx];
        }

        block.sync();
    }

    if (row < M && col < N) {
        C[row * N + col] = sum;
    }
}

// ============================================================================
// Cooperative Groups: Prefix Sum (Scan)
// ============================================================================

/**
 * Inclusive scan using cooperative groups (warp-level)
 *
 * Uses warp shuffle for efficient prefix sum within a warp.
 */
__device__ float warp_scan_inclusive_cg(cg::thread_block_tile<32> warp, float value) {
    // Warp-level inclusive scan using shuffle
    for (int offset = 1; offset < warp.size(); offset *= 2) {
        float other = warp.shfl_up(value, offset);
        if (warp.thread_rank() >= offset) {
            value += other;
        }
    }
    return value;
}

/**
 * Block-level inclusive scan using cooperative groups
 *
 * Two-level approach:
 * 1. Warp-level scan using shuffles
 * 2. Inter-warp aggregation using shared memory
 */
template<int BLOCK_SIZE>
__global__ void scan_cg_inclusive(const float* __restrict__ input,
                                   float* __restrict__ output,
                                   float* __restrict__ block_aggregates,
                                   int n) {
    cg::thread_block block = cg::this_thread_block();
    cg::thread_block_tile<32> warp = cg::tiled_partition<32>(block);

    __shared__ float warp_sums[BLOCK_SIZE / 32];

    int tid = block.thread_rank();
    int gid = blockIdx.x * BLOCK_SIZE + tid;

    // Load data
    float value = (gid < n) ? input[gid] : 0.0f;

    // Level 1: Warp-level inclusive scan
    float warp_scan_result = warp_scan_inclusive_cg(warp, value);

    // Each warp writes its total
    if (warp.thread_rank() == warp.size() - 1) {
        warp_sums[warp.meta_group_rank()] = warp_scan_result;
    }
    block.sync();

    // Level 2: Scan the warp sums (single warp)
    if (tid < BLOCK_SIZE / 32) {
        float warp_sum = warp_sums[tid];
        warp_sum = warp_scan_inclusive_cg(warp, warp_sum);
        warp_sums[tid] = warp_sum;
    }
    block.sync();

    // Add preceding warp sums
    float block_scan_result = warp_scan_result;
    if (warp.meta_group_rank() > 0) {
        block_scan_result += warp_sums[warp.meta_group_rank() - 1];
    }

    // Write result
    if (gid < n) {
        output[gid] = block_scan_result;
    }

    // Write block aggregate for multi-block scan
    if (tid == BLOCK_SIZE - 1 && block_aggregates != nullptr) {
        block_aggregates[blockIdx.x] = block_scan_result;
    }
}

/**
 * Exclusive scan (prefix sum excluding current element)
 */
template<int BLOCK_SIZE>
__global__ void scan_cg_exclusive(const float* __restrict__ input,
                                   float* __restrict__ output,
                                   int n) {
    cg::thread_block block = cg::this_thread_block();
    cg::thread_block_tile<32> warp = cg::tiled_partition<32>(block);

    __shared__ float warp_sums[BLOCK_SIZE / 32];

    int tid = block.thread_rank();
    int gid = blockIdx.x * BLOCK_SIZE + tid;

    float value = (gid < n) ? input[gid] : 0.0f;

    // Warp-level inclusive scan
    float warp_inc = warp_scan_inclusive_cg(warp, value);

    // Convert to exclusive by shifting
    float warp_exc = warp.shfl_up(warp_inc, 1);
    if (warp.thread_rank() == 0) {
        warp_exc = 0.0f;
    }

    // Warp aggregates
    if (warp.thread_rank() == warp.size() - 1) {
        warp_sums[warp.meta_group_rank()] = warp_inc;
    }
    block.sync();

    // Scan warp sums
    if (tid < BLOCK_SIZE / 32) {
        float sum = warp_sums[tid];
        sum = warp_scan_inclusive_cg(warp, sum);
        if (warp.thread_rank() > 0) {
            sum = warp.shfl_up(sum, 1);
        } else {
            sum = 0.0f;
        }
        warp_sums[tid] = sum;
    }
    block.sync();

    // Add preceding warp sums
    float result = warp_exc;
    if (warp.meta_group_rank() > 0) {
        result += warp_sums[warp.meta_group_rank()];
    }

    if (gid < n) {
        output[gid] = result;
    }
}

// ============================================================================
// Cooperative Groups: Dot Product with Tiled Reduction
// ============================================================================

/**
 * Dot product using cooperative groups with hierarchical reduction
 *
 * Demonstrates combining multiple cooperative group types:
 * - Thread blocks for overall structure
 * - Warps for efficient shuffle-based reduction
 * - Tiles for flexible group sizes
 */
template<int BLOCK_SIZE>
__global__ void dot_product_cg(const float* __restrict__ a,
                                const float* __restrict__ b,
                                float* __restrict__ result,
                                int n) {
    cg::thread_block block = cg::this_thread_block();
    cg::thread_block_tile<32> warp = cg::tiled_partition<32>(block);

    int tid = block.thread_rank();
    int gid = blockIdx.x * BLOCK_SIZE + tid;

    // Compute partial dot product
    float partial_sum = 0.0f;
    for (int i = gid; i < n; i += gridDim.x * BLOCK_SIZE) {
        partial_sum += a[i] * b[i];
    }

    // Warp-level reduction
    for (int offset = warp.size() / 2; offset > 0; offset >>= 1) {
        partial_sum += warp.shfl_down(partial_sum, offset);
    }

    // Shared memory for inter-warp communication
    __shared__ float warp_results[BLOCK_SIZE / 32];

    if (warp.thread_rank() == 0) {
        warp_results[warp.meta_group_rank()] = partial_sum;
    }
    block.sync();

    // Final reduction by first warp
    if (tid < BLOCK_SIZE / 32) {
        float final_sum = warp_results[tid];
        for (int offset = (BLOCK_SIZE / 32) / 2; offset > 0; offset >>= 1) {
            final_sum += warp.shfl_down(final_sum, offset);
        }

        if (tid == 0) {
            atomicAdd(result, final_sum);
        }
    }
}

// ============================================================================
// Explicit Template Instantiations
// ============================================================================

template __global__ void bitonic_sort_cg<256>(int*, int);
template __global__ void histogram_cg_warp_aggregated<256, 256>(const int*, int*, int);
template __global__ void histogram_cg_labeled<256>(const int*, int*, int, int);
template __global__ void matrix_transpose_cg<16>(const float*, float*, int, int);
template __global__ void matrix_transpose_cg<32>(const float*, float*, int, int);
template __global__ void matrix_multiply_cg<16>(const float*, const float*, float*, int, int, int);
template __global__ void matrix_multiply_cg<32>(const float*, const float*, float*, int, int, int);
template __global__ void scan_cg_inclusive<256>(const float*, float*, float*, int);
template __global__ void scan_cg_exclusive<256>(const float*, float*, int);
template __global__ void dot_product_cg<256>(const float*, const float*, float*, int);
