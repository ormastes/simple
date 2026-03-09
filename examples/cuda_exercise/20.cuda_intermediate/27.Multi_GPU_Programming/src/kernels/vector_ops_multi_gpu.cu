/**
 * Multi-GPU Vector Operations (Module 27)
 *
 * This file extends Module 26's cooperative groups vector operations
 * to support multi-GPU execution with the following improvements:
 *
 * Enhancements over Module 26 (Single GPU):
 * 1. Distributed data across multiple GPUs
 * 2. Tree-based multi-GPU reduction
 * 3. Peer-to-peer communication for reduction
 * 4. Multi-GPU histogram with distributed bins
 * 5. Concurrent execution with minimal synchronization
 *
 * Multi-GPU strategies:
 * - Data parallelism: Distribute elements across GPUs
 * - Tree reduction: Hierarchical combining across GPUs
 * - Load balancing: Distribute work based on GPU capabilities
 * - Asynchronous P2P transfers for minimal overhead
 */

#include <cuda_runtime.h>
#include <cooperative_groups.h>
#include <cstdint>

namespace cg = cooperative_groups;

// ============================================================================
// Multi-GPU Reduction (Local Phase)
// ============================================================================

/**
 * Local reduction phase on each GPU
 *
 * Each GPU reduces its portion of data to a single value
 * This is the first phase of multi-GPU reduction
 */
template<int BLOCK_SIZE>
__global__ void reduction_local_multi_gpu(
    const float* __restrict__ input_local,  // Local portion of data
    float* __restrict__ output,              // Single output value per GPU
    int n_local                              // Number of elements on this GPU
) {
    cg::thread_block block = cg::this_thread_block();
    cg::thread_block_tile<32> warp = cg::tiled_partition<32>(block);

    __shared__ float warp_results[BLOCK_SIZE / 32];

    int tid = threadIdx.x;
    int gid = blockIdx.x * BLOCK_SIZE + threadIdx.x;

    // Grid-stride loop to handle all local data
    float sum = 0.0f;
    for (int i = gid; i < n_local; i += gridDim.x * BLOCK_SIZE) {
        sum += input_local[i];
    }

    // Warp-level reduction using shuffle
    for (int offset = warp.size() / 2; offset > 0; offset >>= 1) {
        sum += warp.shfl_down(sum, offset);
    }

    // First thread of each warp writes to shared memory
    if (warp.thread_rank() == 0) {
        warp_results[warp.meta_group_rank()] = sum;
    }
    block.sync();

    // First warp reduces warp results
    if (tid < BLOCK_SIZE / 32) {
        sum = warp_results[tid];

        for (int offset = warp.size() / 2; offset > 0; offset >>= 1) {
            sum += warp.shfl_down(sum, offset);
        }

        if (tid == 0) {
            atomicAdd(output, sum);
        }
    }
}

// ============================================================================
// Multi-GPU Reduction (Tree Combine)
// ============================================================================

/**
 * Tree-based reduction kernel for combining results from multiple GPUs
 *
 * Input: Array of partial results from all GPUs
 * Output: Final combined result
 *
 * This kernel runs on GPU 0 to combine all partial results
 */
__global__ void reduction_tree_combine(
    float* __restrict__ partial_results,  // Array of results from all GPUs
    float* __restrict__ final_result,     // Single final result
    int num_gpus
) {
    cg::thread_block block = cg::this_thread_block();
    cg::thread_block_tile<32> warp = cg::tiled_partition<32>(block);

    __shared__ float shared_data[256];

    int tid = threadIdx.x;

    // Load partial results
    float sum = 0.0f;
    if (tid < num_gpus) {
        sum = partial_results[tid];
    }

    shared_data[tid] = sum;
    block.sync();

    // Reduce within block
    for (int stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (tid < stride && tid + stride < num_gpus) {
            shared_data[tid] += shared_data[tid + stride];
        }
        block.sync();
    }

    if (tid == 0) {
        *final_result = shared_data[0];
    }
}

// ============================================================================
// Multi-GPU Histogram (Distributed Bins)
// ============================================================================

/**
 * Multi-GPU histogram with distributed bins
 *
 * Strategy 1: Each GPU maintains full histogram and merge at end
 * Strategy 2: Distribute bins across GPUs (more complex but better scaling)
 *
 * This implements Strategy 1 with warp aggregation
 */
template<int BLOCK_SIZE, int NUM_BINS>
__global__ void histogram_local_multi_gpu(
    const int* __restrict__ data_local,  // Local portion of data
    int* __restrict__ histogram_local,   // Local histogram (full bins)
    int n_local
) {
    cg::thread_block block = cg::this_thread_block();
    cg::thread_block_tile<32> warp = cg::tiled_partition<32>(block);

    __shared__ int smem_hist[NUM_BINS];

    // Initialize shared histogram
    for (int i = threadIdx.x; i < NUM_BINS; i += BLOCK_SIZE) {
        smem_hist[i] = 0;
    }
    block.sync();

    // Process local data with warp aggregation
    for (int gid = blockIdx.x * BLOCK_SIZE + threadIdx.x;
         gid < n_local;
         gid += gridDim.x * BLOCK_SIZE) {

        int value = data_local[gid];
        int bin = value % NUM_BINS;

        // Warp aggregation: count how many threads in warp have same bin
        for (int i = 0; i < NUM_BINS; i++) {
            unsigned int mask = warp.ballot(bin == i);
            int count = __popc(mask);

            // Only leader does atomic
            if (bin == i && warp.thread_rank() == __ffs(mask) - 1) {
                atomicAdd(&smem_hist[i], count);
            }
        }
    }

    block.sync();

    // Merge to global histogram
    for (int i = threadIdx.x; i < NUM_BINS; i += BLOCK_SIZE) {
        if (smem_hist[i] > 0) {
            atomicAdd(&histogram_local[i], smem_hist[i]);
        }
    }
}

/**
 * Merge histograms from all GPUs
 *
 * Combines NUM_GPUS histograms into a single final histogram
 * Runs on GPU 0
 */
template<int NUM_BINS>
__global__ void histogram_merge_multi_gpu(
    int** __restrict__ histograms_per_gpu,  // Array of pointers to each GPU's histogram
    int* __restrict__ final_histogram,       // Final merged histogram
    int num_gpus
) {
    int bin = blockIdx.x * blockDim.x + threadIdx.x;

    if (bin < NUM_BINS) {
        int total = 0;
        for (int gpu = 0; gpu < num_gpus; gpu++) {
            total += histograms_per_gpu[gpu][bin];
        }
        final_histogram[bin] = total;
    }
}

// ============================================================================
// Multi-GPU Scan (Prefix Sum)
// ============================================================================

/**
 * Local scan phase on each GPU
 *
 * Each GPU computes prefix sum of its portion
 * Also outputs the total sum for this GPU (needed for global scan)
 */
template<int BLOCK_SIZE>
__global__ void scan_local_multi_gpu(
    const float* __restrict__ input_local,
    float* __restrict__ output_local,
    float* __restrict__ block_sums,
    int n_local
) {
    cg::thread_block block = cg::this_thread_block();
    cg::thread_block_tile<32> warp = cg::tiled_partition<32>(block);

    __shared__ float warp_totals[BLOCK_SIZE / 32];

    int tid = threadIdx.x;
    int gid = blockIdx.x * BLOCK_SIZE + tid;

    // Load data
    float value = (gid < n_local) ? input_local[gid] : 0.0f;

    // Warp-level inclusive scan
    for (int offset = 1; offset < warp.size(); offset *= 2) {
        float other = warp.shfl_up(value, offset);
        if (warp.thread_rank() >= offset) {
            value += other;
        }
    }

    // Store warp totals
    if (warp.thread_rank() == 31) {
        warp_totals[warp.meta_group_rank()] = value;
    }
    block.sync();

    // First warp scans warp totals
    if (tid < BLOCK_SIZE / 32) {
        float total = warp_totals[tid];

        for (int offset = 1; offset < warp.size(); offset *= 2) {
            float other = warp.shfl_up(total, offset);
            if (warp.thread_rank() >= offset) {
                total += other;
            }
        }

        warp_totals[tid] = total;
    }
    block.sync();

    // Add preceding warp totals
    if (warp.meta_group_rank() > 0) {
        value += warp_totals[warp.meta_group_rank() - 1];
    }

    // Write output
    if (gid < n_local) {
        output_local[gid] = value;
    }

    // Save block sum
    if (tid == BLOCK_SIZE - 1) {
        block_sums[blockIdx.x] = value;
    }
}

/**
 * Add global offset to each GPU's scan results
 *
 * After local scans are complete, this kernel adds the cumulative sum
 * from all previous GPUs to each GPU's results
 */
__global__ void scan_add_offset_multi_gpu(
    float* __restrict__ output_local,
    float offset,
    int n_local
) {
    int gid = blockIdx.x * blockDim.x + threadIdx.x;

    if (gid < n_local) {
        output_local[gid] += offset;
    }
}

// ============================================================================
// Multi-GPU Dot Product
// ============================================================================

/**
 * Local dot product phase on each GPU
 *
 * Each GPU computes dot product of its portions of vectors A and B
 */
template<int BLOCK_SIZE>
__global__ void dot_product_local_multi_gpu(
    const float* __restrict__ a_local,
    const float* __restrict__ b_local,
    float* __restrict__ result,
    int n_local
) {
    cg::thread_block block = cg::this_thread_block();
    cg::thread_block_tile<32> warp = cg::tiled_partition<32>(block);

    __shared__ float warp_results[BLOCK_SIZE / 32];

    int gid = blockIdx.x * BLOCK_SIZE + threadIdx.x;

    // Compute partial product
    float sum = 0.0f;
    for (int i = gid; i < n_local; i += gridDim.x * BLOCK_SIZE) {
        sum += a_local[i] * b_local[i];
    }

    // Warp-level reduction
    for (int offset = warp.size() / 2; offset > 0; offset >>= 1) {
        sum += warp.shfl_down(sum, offset);
    }

    if (warp.thread_rank() == 0) {
        warp_results[warp.meta_group_rank()] = sum;
    }
    block.sync();

    // First warp reduces warp results
    if (threadIdx.x < BLOCK_SIZE / 32) {
        sum = warp_results[threadIdx.x];

        for (int offset = warp.size() / 2; offset > 0; offset >>= 1) {
            sum += warp.shfl_down(sum, offset);
        }

        if (threadIdx.x == 0) {
            atomicAdd(result, sum);
        }
    }
}

// ============================================================================
// Multi-GPU Vector Addition
// ============================================================================

/**
 * Simple element-wise vector addition on local data
 *
 * Each GPU processes its portion independently
 */
__global__ void vector_add_multi_gpu(
    const float* __restrict__ a_local,
    const float* __restrict__ b_local,
    float* __restrict__ c_local,
    int n_local
) {
    int gid = blockIdx.x * blockDim.x + threadIdx.x;

    if (gid < n_local) {
        c_local[gid] = a_local[gid] + b_local[gid];
    }
}

// Explicit template instantiations
template __global__ void reduction_local_multi_gpu<256>(const float*, float*, int);
template __global__ void histogram_local_multi_gpu<256, 256>(const int*, int*, int);
template __global__ void histogram_merge_multi_gpu<256>(int**, int*, int);
template __global__ void scan_local_multi_gpu<256>(const float*, float*, float*, int);
template __global__ void dot_product_local_multi_gpu<256>(const float*, const float*, float*, int);
