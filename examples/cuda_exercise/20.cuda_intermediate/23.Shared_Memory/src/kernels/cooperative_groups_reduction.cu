/**
 * Reduction with Cooperative Groups (Module 23 + Module 25 Enhanced)
 *
 * This file demonstrates using CUDA Cooperative Groups to improve upon
 * Module 25's dynamic parallelism patterns with better synchronization control.
 *
 * Cooperative Groups Features:
 * 1. Thread Block Groups - Fine-grained thread group management
 * 2. Tiled Partitions - Warp-level collectives
 * 3. Grid Groups - Entire grid synchronization
 * 4. Flexible synchronization - Beyond __syncthreads()
 *
 * Improvements over Module 25:
 * - Explicit thread group management
 * - Warp-level primitives for reduction
 * - Multi-grid synchronization
 * - Better composability and code reuse
 */

#include <cuda_runtime.h>
#include <cooperative_groups.h>
#include <cooperative_groups/reduce.h>
#include <cstdint>

namespace cg = cooperative_groups;

// ============================================================================
// Cooperative Groups: Thread Block Reduction
// ============================================================================

/**
 * Reduction using thread_block cooperative group
 *
 * Benefits over __syncthreads():
 * - More explicit about synchronization domain
 * - Can create sub-groups for partial synchronization
 * - Enables grid-wide operations
 */
template<int BLOCK_SIZE>
__global__ void reduction_cg_thread_block(const float* __restrict__ input,
                                           float* __restrict__ output,
                                           int n) {
    // Get thread block group - represents all threads in this block
    cg::thread_block block = cg::this_thread_block();

    __shared__ float sdata[BLOCK_SIZE];

    int tid = block.thread_rank();  // Thread index within block
    int gid = block.group_index().x * block.size() + tid;  // Global thread ID

    // Load data into shared memory with vectorized access
    float sum = 0.0f;
    if (gid < n) sum += input[gid];
    if (gid + BLOCK_SIZE < n) sum += input[gid + BLOCK_SIZE];
    if (gid + 2 * BLOCK_SIZE < n) sum += input[gid + 2 * BLOCK_SIZE];
    if (gid + 3 * BLOCK_SIZE < n) sum += input[gid + 3 * BLOCK_SIZE];

    sdata[tid] = sum;
    block.sync();  // Equivalent to __syncthreads() but more explicit

    // Reduction using thread_block synchronization
    for (int s = BLOCK_SIZE / 2; s > 32; s >>= 1) {
        if (tid < s) {
            sdata[tid] += sdata[tid + s];
        }
        block.sync();  // Synchronize all threads in block
    }

    // Final warp reduction (no sync needed within warp)
    if (tid < 32) {
        if (BLOCK_SIZE >= 64) { sdata[tid] += sdata[tid + 32]; cg::sync(cg::coalesced_threads()); }
        if (BLOCK_SIZE >= 32) { sdata[tid] += sdata[tid + 16]; cg::sync(cg::coalesced_threads()); }
        if (BLOCK_SIZE >= 16) { sdata[tid] += sdata[tid + 8];  cg::sync(cg::coalesced_threads()); }
        if (BLOCK_SIZE >= 8)  { sdata[tid] += sdata[tid + 4];  cg::sync(cg::coalesced_threads()); }
        if (BLOCK_SIZE >= 4)  { sdata[tid] += sdata[tid + 2];  cg::sync(cg::coalesced_threads()); }
        if (BLOCK_SIZE >= 2)  { sdata[tid] += sdata[tid + 1];  cg::sync(cg::coalesced_threads()); }
    }

    if (tid == 0) {
        output[block.group_index().x] = sdata[0];
    }
}

// ============================================================================
// Cooperative Groups: Tiled Partition (Warp-Level Reduction)
// ============================================================================

/**
 * Warp-level reduction using tiled partition
 *
 * Tiled partitions enable warp-level collective operations.
 * This is more efficient than traditional warp reduction.
 */
__device__ float warp_reduce_cg(cg::thread_block_tile<32> tile, float val) {
    // Warp-level reduction using shuffle intrinsics
    for (int offset = tile.size() / 2; offset > 0; offset >>= 1) {
        val += tile.shfl_down(val, offset);  // Shuffle data down within tile
    }
    return val;
}

/**
 * Reduction using tiled partitions for warp-level collectives
 *
 * Advantages:
 * - Uses shuffle intrinsics (faster than shared memory)
 * - No shared memory bank conflicts
 * - Explicit warp-level synchronization
 */
template<int BLOCK_SIZE>
__global__ void reduction_cg_tiled(const float* __restrict__ input,
                                    float* __restrict__ output,
                                    int n) {
    cg::thread_block block = cg::this_thread_block();

    // Create a tiled partition of 32 threads (warp size)
    cg::thread_block_tile<32> warp = cg::tiled_partition<32>(block);

    int tid = block.thread_rank();
    int gid = blockIdx.x * (BLOCK_SIZE * 4) + tid;

    // Vectorized load and first reduction
    float sum = 0.0f;
    if (gid < n) sum += input[gid];
    if (gid + BLOCK_SIZE < n) sum += input[gid + BLOCK_SIZE];
    if (gid + 2 * BLOCK_SIZE < n) sum += input[gid + 2 * BLOCK_SIZE];
    if (gid + 3 * BLOCK_SIZE < n) sum += input[gid + 3 * BLOCK_SIZE];

    // Warp-level reduction using shuffle
    sum = warp_reduce_cg(warp, sum);

    // Shared memory for inter-warp communication
    __shared__ float warp_results[BLOCK_SIZE / 32];

    // Each warp writes its result
    if (warp.thread_rank() == 0) {
        warp_results[warp.meta_group_rank()] = sum;
    }
    block.sync();

    // First warp reduces the warp results
    if (tid < BLOCK_SIZE / 32) {
        sum = warp_results[tid];
        sum = warp_reduce_cg(warp, sum);

        if (tid == 0) {
            output[blockIdx.x] = sum;
        }
    }
}

// ============================================================================
// Cooperative Groups: Coalesced Threads
// ============================================================================

/**
 * Reduction using coalesced threads group
 *
 * Coalesced threads represent currently active threads in a warp.
 * This is useful when threads are divergent.
 */
template<int BLOCK_SIZE>
__global__ void reduction_cg_coalesced(const float* __restrict__ input,
                                        float* __restrict__ output,
                                        int n,
                                        int threshold) {
    cg::thread_block block = cg::this_thread_block();

    int tid = block.thread_rank();
    int gid = blockIdx.x * BLOCK_SIZE + tid;

    __shared__ float sdata[BLOCK_SIZE];

    // Conditional loading - creates divergence
    float value = 0.0f;
    if (gid < n) {
        value = input[gid];

        // Apply conditional threshold (creates divergent branches)
        if (value > threshold) {
            value *= 2.0f;
        } else {
            value *= 0.5f;
        }
    }

    sdata[tid] = value;
    block.sync();

    // Reduction with potentially divergent threads
    for (int s = BLOCK_SIZE / 2; s > 32; s >>= 1) {
        if (tid < s) {
            sdata[tid] += sdata[tid + s];
        }
        block.sync();
    }

    // Final warp reduction using coalesced threads
    if (tid < 32) {
        // Get the group of currently active threads
        cg::coalesced_group active = cg::coalesced_threads();

        // Reduce among active threads only
        float warp_sum = sdata[tid];
        for (int offset = 16; offset > 0; offset >>= 1) {
            if (active.thread_rank() < offset) {
                warp_sum += sdata[tid + offset];
                sdata[tid] = warp_sum;
            }
            active.sync();
        }
    }

    if (tid == 0) {
        output[blockIdx.x] = sdata[0];
    }
}

// ============================================================================
// Cooperative Groups: Multi-Block Reduction (Grid Group)
// ============================================================================

/**
 * Grid-wide reduction using cooperative groups
 *
 * Requires:
 * - Kernel launched with cudaLaunchCooperativeKernel()
 * - Device supports cooperative groups
 * - All blocks must reach grid.sync()
 *
 * This eliminates need for multiple kernel launches or atomics.
 */
template<int BLOCK_SIZE>
__global__ void reduction_cg_grid(float* __restrict__ data,
                                   float* __restrict__ temp,
                                   int n) {
    // Get grid-wide cooperative group
    cg::grid_group grid = cg::this_grid();
    cg::thread_block block = cg::this_thread_block();

    int tid = block.thread_rank();
    int gid = grid.thread_rank();  // Global thread index across entire grid

    __shared__ float sdata[BLOCK_SIZE];

    // Load and reduce multiple elements per thread
    float sum = 0.0f;
    for (int i = gid; i < n; i += grid.size()) {
        sum += data[i];
    }

    sdata[tid] = sum;
    block.sync();

    // Block-level reduction
    for (int s = BLOCK_SIZE / 2; s > 0; s >>= 1) {
        if (tid < s) {
            sdata[tid] += sdata[tid + s];
        }
        block.sync();
    }

    // Write block result to temporary array
    if (tid == 0) {
        temp[block.group_index().x] = sdata[0];
    }

    // Grid-wide synchronization - ALL blocks must reach this point!
    grid.sync();

    // First block reduces all block results
    if (block.group_index().x == 0) {
        int num_blocks = gridDim.x;  // Total number of blocks

        // Load block results
        sum = (tid < num_blocks) ? temp[tid] : 0.0f;
        sdata[tid] = sum;
        block.sync();

        // Final reduction
        for (int s = BLOCK_SIZE / 2; s > 0; s >>= 1) {
            if (tid < s && tid + s < num_blocks) {
                sdata[tid] += sdata[tid + s];
            }
            block.sync();
        }

        // Write final result
        if (tid == 0) {
            data[0] = sdata[0];
        }
    }
}

// ============================================================================
// Cooperative Groups: Segmented Reduction
// ============================================================================

/**
 * Segmented reduction using labeled partitions
 *
 * Each segment is reduced independently using cooperative groups.
 * This improves upon Module 25's segmented reduction with better sync.
 */
template<int BLOCK_SIZE>
__global__ void reduction_cg_segmented(const float* __restrict__ input,
                                        float* __restrict__ output,
                                        const int* __restrict__ segment_ids,
                                        const int* __restrict__ segment_offsets,
                                        int num_segments,
                                        int n) {
    cg::thread_block block = cg::this_thread_block();
    cg::thread_block_tile<32> warp = cg::tiled_partition<32>(block);

    int gid = blockIdx.x * BLOCK_SIZE + threadIdx.x;

    if (gid >= n) return;

    // Get segment ID for this element
    int seg_id = segment_ids[gid];
    int seg_start = segment_offsets[seg_id];
    int seg_end = (seg_id + 1 < num_segments) ? segment_offsets[seg_id + 1] : n;

    float value = input[gid];

    // Warp-level segmented reduction
    // Threads in same segment within a warp collaborate
    for (int offset = 1; offset < warp.size(); offset *= 2) {
        float other_val = warp.shfl_up(value, offset);
        int other_seg = warp.shfl_up(seg_id, offset);

        // Only add if same segment
        if (warp.thread_rank() >= offset && other_seg == seg_id) {
            value += other_val;
        }
    }

    // Last thread of each segment in warp writes result
    int next_seg = warp.shfl_down(seg_id, 1);
    bool is_segment_end = (warp.thread_rank() == warp.size() - 1) || (next_seg != seg_id);

    if (is_segment_end) {
        // Atomic add for cross-warp segments
        atomicAdd(&output[seg_id], value);
    }
}

// ============================================================================
// Cooperative Groups: Hierarchical Reduction (Multi-Level)
// ============================================================================

/**
 * Hierarchical reduction using nested cooperative groups
 *
 * Demonstrates using multiple group levels:
 * - Thread blocks for coarse-grained parallelism
 * - Warps for mid-level reduction
 * - Tiles for fine-grained control
 */
template<int BLOCK_SIZE, int TILE_SIZE>
__global__ void reduction_cg_hierarchical(const float* __restrict__ input,
                                           float* __restrict__ output,
                                           int n) {
    cg::thread_block block = cg::this_thread_block();
    cg::thread_block_tile<TILE_SIZE> tile = cg::tiled_partition<TILE_SIZE>(block);

    int tid = block.thread_rank();
    int gid = blockIdx.x * BLOCK_SIZE + tid;

    // Load data
    float value = (gid < n) ? input[gid] : 0.0f;

    // Level 1: Tile-level reduction (e.g., 4-thread tiles)
    for (int offset = tile.size() / 2; offset > 0; offset >>= 1) {
        value += tile.shfl_down(value, offset);
    }

    // Shared memory for inter-tile communication
    __shared__ float tile_results[BLOCK_SIZE / TILE_SIZE];

    // Each tile leader writes result
    if (tile.thread_rank() == 0) {
        tile_results[tile.meta_group_rank()] = value;
    }
    block.sync();

    // Level 2: Warp-level reduction of tile results
    if (tid < BLOCK_SIZE / TILE_SIZE) {
        cg::thread_block_tile<32> warp = cg::tiled_partition<32>(block);

        float warp_val = tile_results[tid];
        for (int offset = warp.size() / 2; offset > 0; offset >>= 1) {
            warp_val += warp.shfl_down(warp_val, offset);
        }

        if (warp.thread_rank() == 0) {
            output[blockIdx.x] = warp_val;
        }
    }
}

// ============================================================================
// Utility: Check Device Support for Cooperative Groups
// ============================================================================

/**
 * Check if device supports cooperative kernel launch
 * Required for grid-wide synchronization
 */
__host__ bool supports_cooperative_launch(int device = 0) {
    cudaDeviceProp props;
    cudaGetDeviceProperties(&props, device);

    return props.cooperativeLaunch == 1;
}

/**
 * Get maximum blocks for cooperative launch
 * Returns the maximum number of blocks that can participate in grid.sync()
 */
__host__ int get_max_cooperative_blocks(int device, void* kernel, int block_size, int dynamic_smem) {
    int num_blocks_per_sm = 0;
    cudaOccupancyMaxActiveBlocksPerMultiprocessor(
        &num_blocks_per_sm,
        kernel,
        block_size,
        dynamic_smem
    );

    cudaDeviceProp props;
    cudaGetDeviceProperties(&props, device);

    return num_blocks_per_sm * props.multiProcessorCount;
}

// Explicit template instantiations for common block sizes
template __global__ void reduction_cg_thread_block<256>(const float*, float*, int);
template __global__ void reduction_cg_tiled<256>(const float*, float*, int);
template __global__ void reduction_cg_coalesced<256>(const float*, float*, int, int);
template __global__ void reduction_cg_grid<256>(float*, float*, int);
template __global__ void reduction_cg_segmented<256>(const float*, float*, const int*, const int*, int, int);
template __global__ void reduction_cg_hierarchical<256, 4>(const float*, float*, int);
template __global__ void reduction_cg_hierarchical<256, 8>(const float*, float*, int);
template __global__ void reduction_cg_hierarchical<256, 16>(const float*, float*, int);
template __global__ void reduction_cg_hierarchical<256, 32>(const float*, float*, int);
