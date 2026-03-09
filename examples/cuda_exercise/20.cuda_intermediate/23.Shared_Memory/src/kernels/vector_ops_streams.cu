/**
 * Vector Operations with Streams and Async Execution (Part 22)
 *
 * Enhancements over Part 21:
 * - Stream-based chunked processing for large vectors
 * - Asynchronous reductions with event synchronization
 * - Pipeline patterns for continuous data flow
 * - Multi-stream histogram with dynamic parallelism
 * - Stream callbacks for CPU-GPU coordination
 * - Prefetching with unified memory
 *
 * Combines Part 21's atomic/sync operations with Part 22's streaming
 */

#include <cuda_runtime.h>
#include <cooperative_groups.h>
#include <cooperative_groups/reduce.h>
#include "cuda_utils.h"  // From CudaCustomLib, via CMake target_link_libraries

namespace cg = cooperative_groups;

// =============================================================================
// Chunked Vector Addition with Streams
// =============================================================================

/**
 * Processes vector chunks concurrently across multiple streams
 * Optimal for very large vectors that don't fit in single kernel launch
 */
__global__ void vector_add_chunk(const float* a, const float* b, float* c,
                                 int chunk_size, int chunk_offset) {
    int local_idx = blockIdx.x * blockDim.x + threadIdx.x;
    int global_idx = chunk_offset + local_idx;

    if (local_idx < chunk_size) {
        c[global_idx] = a[global_idx] + b[global_idx];
    }
}

// =============================================================================
// Pipeline Reduction with Streams
// =============================================================================

/**
 * Stage 1: Partial reduction within each stream's chunk
 */
__global__ void reduction_stage1(const float* input, float* partial_sums,
                                 int chunk_size, int chunk_offset) {
    extern __shared__ float sdata[];

    int tid = threadIdx.x;
    int global_idx = chunk_offset + blockIdx.x * blockDim.x + tid;

    // Load data
    sdata[tid] = (global_idx < chunk_offset + chunk_size) ? input[global_idx] : 0.0f;
    __syncthreads();

    // Block-level reduction
    for (int stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (tid < stride) {
            sdata[tid] += sdata[tid + stride];
        }
        __syncthreads();
    }

    // Write partial result
    if (tid == 0) {
        atomicAdd(partial_sums, sdata[0]);
    }
}

/**
 * Stage 2: Final reduction of partial sums from all streams
 * Uses warp shuffle from Part 21 for efficiency
 */
__device__ float warp_reduce(float val) {
    for (int offset = warpSize / 2; offset > 0; offset /= 2) {
        val += __shfl_down_sync(0xffffffff, val, offset);
    }
    return val;
}

__global__ void reduction_stage2(const float* partial_sums, float* result,
                                 int num_partials) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    int lane = threadIdx.x % warpSize;

    float val = (tid < num_partials) ? partial_sums[tid] : 0.0f;

    // Warp-level reduction
    val = warp_reduce(val);

    // First thread of each warp accumulates
    if (lane == 0) {
        atomicAdd(result, val);
    }
}

// =============================================================================
// Async Histogram with Dynamic Streams
// =============================================================================

/**
 * Computes histogram using multiple streams for different data ranges
 * Uses shared memory atomics from Part 21 for efficiency
 */
__global__ void histogram_chunk(const int* input, int* histogram,
                                int num_bins, int chunk_size, int chunk_offset) {
    extern __shared__ int shared_hist[];

    int tid = threadIdx.x;
    int global_idx = chunk_offset + blockIdx.x * blockDim.x + tid;

    // Initialize shared histogram
    for (int bin = tid; bin < num_bins; bin += blockDim.x) {
        shared_hist[bin] = 0;
    }
    __syncthreads();

    // Accumulate in shared memory
    if (global_idx < chunk_offset + chunk_size) {
        int bin = input[global_idx] % num_bins;
        atomicAdd(&shared_hist[bin], 1);
    }
    __syncthreads();

    // Write back to global memory
    for (int bin = tid; bin < num_bins; bin += blockDim.x) {
        atomicAdd(&histogram[bin], shared_hist[bin]);
    }
}

// =============================================================================
// Double Buffered Vector Processing
// =============================================================================

/**
 * Processes vector with double buffering to overlap H2D and computation
 * Buffer selection based on stream ID for concurrent execution
 */
__global__ void vector_process_buffered(float* buffer, int size,
                                        float factor, int buffer_id) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < size) {
        float val = buffer[idx];

        // Compute-intensive operation
        for (int i = 0; i < 50; i++) {
            val = sinf(val * factor) + cosf(val);
        }

        buffer[idx] = val;
    }
}

// =============================================================================
// Event-Based Producer-Consumer Pattern
// =============================================================================

/**
 * Producer: Generates data in one stream
 */
__global__ void vector_producer(float* output, int size, int offset,
                                float base_value) {
    int local_idx = blockIdx.x * blockDim.x + threadIdx.x;
    int global_idx = offset + local_idx;

    if (local_idx < size) {
        // Simulate data generation
        output[global_idx] = base_value + (float)global_idx * 0.01f;
    }
}

/**
 * Consumer: Processes data produced by another stream
 * Synchronization handled by CUDA events
 */
__global__ void vector_consumer(const float* input, float* output,
                                int size, int offset) {
    int local_idx = blockIdx.x * blockDim.x + threadIdx.x;
    int global_idx = offset + local_idx;

    if (local_idx < size) {
        // Process produced data
        float val = input[global_idx];
        output[global_idx] = sqrtf(val * val + 1.0f);
    }
}

// =============================================================================
// Multi-Stream Dot Product with Cooperative Groups
// =============================================================================

/**
 * Computes partial dot products in parallel streams
 * Uses cooperative groups from Part 21 for reduction
 */
__global__ void dot_product_chunk(const float* a, const float* b,
                                  float* partial_results,
                                  int chunk_size, int chunk_offset,
                                  int stream_id) {
    cg::thread_block block = cg::this_thread_block();
    cg::thread_block_tile<32> tile = cg::tiled_partition<32>(block);

    int local_idx = blockIdx.x * blockDim.x + threadIdx.x;
    int global_idx = chunk_offset + local_idx;

    // Compute partial dot product
    float partial = 0.0f;
    if (local_idx < chunk_size) {
        partial = a[global_idx] * b[global_idx];
    }

    // Tile-level reduction
    partial = cg::reduce(tile, partial, cg::plus<float>());

    // Accumulate tile results
    __shared__ float tile_sums[32];
    if (tile.thread_rank() == 0) {
        tile_sums[tile.meta_group_rank()] = partial;
    }
    block.sync();

    // Final reduction by first tile
    if (tile.meta_group_rank() == 0) {
        float sum = (tile.thread_rank() < (blockDim.x + 31) / 32) ?
                    tile_sums[tile.thread_rank()] : 0.0f;
        sum = cg::reduce(tile, sum, cg::plus<float>());

        if (tile.thread_rank() == 0) {
            atomicAdd(&partial_results[stream_id], sum);
        }
    }
}

// =============================================================================
// Persistent Thread Pattern with Streams
// =============================================================================

/**
 * Persistent threads process work queue items
 * Different streams can process different priority queues
 */
struct WorkItem {
    float* input;
    float* output;
    int size;
    float factor;
};

__global__ void persistent_vector_processor(WorkItem* work_queue,
                                            volatile int* queue_size,
                                            int max_items) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;

    while (true) {
        // Atomically get next work item
        int item_idx = atomicAdd((int*)queue_size, -1) - 1;

        if (item_idx < 0 || item_idx >= max_items) {
            break;  // No more work
        }

        WorkItem item = work_queue[item_idx];

        // Process this work item
        for (int i = tid; i < item.size; i += gridDim.x * blockDim.x) {
            float val = item.input[i];
            val = val * item.factor + sinf(val);
            item.output[i] = val;
        }
    }
}

// =============================================================================
// Stream Callback Integration Kernel
// =============================================================================

/**
 * Kernel that produces results for stream callback processing
 * Callback on CPU can launch next stage based on results
 */
__global__ void compute_statistics(const float* data, float* mean, float* variance,
                                   int size) {
    extern __shared__ float sdata[];
    float* sum_shared = sdata;
    float* sum_sq_shared = &sdata[blockDim.x];

    int tid = threadIdx.x;
    int idx = blockIdx.x * blockDim.x + tid;

    // Load and compute
    float val = (idx < size) ? data[idx] : 0.0f;
    sum_shared[tid] = val;
    sum_sq_shared[tid] = val * val;
    __syncthreads();

    // Reduce
    for (int stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (tid < stride) {
            sum_shared[tid] += sum_shared[tid + stride];
            sum_sq_shared[tid] += sum_sq_shared[tid + stride];
        }
        __syncthreads();
    }

    if (tid == 0) {
        atomicAdd(mean, sum_shared[0]);
        atomicAdd(variance, sum_sq_shared[0]);
    }
}

// =============================================================================
// Prefetch-Enabled Vector Operations (Unified Memory)
// =============================================================================

/**
 * Works with unified memory and prefetch hints
 * Demonstrates managed memory with streaming
 */
__global__ void vector_transform_managed(float* data, int size, float scale) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < size) {
        // Simple transformation on managed memory
        data[idx] = data[idx] * scale + logf(fabsf(data[idx]) + 1.0f);
    }
}

// =============================================================================
// Graph-Compatible Kernels
// =============================================================================

/**
 * Simple kernel suitable for CUDA graph capture
 * Fixed parameters enable graph optimization
 */
__global__ void vector_scale_graph(float* data, int size, float scale) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < size) {
        data[idx] *= scale;
    }
}

__global__ void vector_add_graph(const float* a, const float* b, float* c, int size) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < size) {
        c[idx] = a[idx] + b[idx];
    }
}

// =============================================================================
// Multi-GPU Stream Coordination (Peer Access)
// =============================================================================

/**
 * Kernel that can work with peer-accessible memory from another GPU
 * Enables multi-GPU streaming patterns
 */
__global__ void vector_add_peer(const float* a, const float* b_peer,
                                float* c, int size) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < size) {
        // b_peer may be on different GPU (if peer access enabled)
        c[idx] = a[idx] + b_peer[idx];
    }
}
