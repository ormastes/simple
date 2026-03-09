/**
 * Vector Addition with Advanced Synchronization (Part 21)
 *
 * Improvements over Part 19:
 * - Warp-level synchronization for efficient reductions
 * - Atomic operations for safe partial sums
 * - Cooperative groups for flexible thread organization
 * - Memory fences for producer-consumer patterns
 * - Lock-free concurrent updates
 *
 * This demonstrates how Part 21's synchronization techniques
 * enhance the vector operations from Part 19.
 */

#include <cuda_runtime.h>
#include <cooperative_groups.h>
#include "cuda_utils.h"  // From CudaCustomLib, via CMake target_link_libraries

namespace cg = cooperative_groups;

// =============================================================================
// Warp-Level Primitives for Vector Reduction
// =============================================================================

/**
 * Vector reduction using warp shuffle - no shared memory needed
 * Performance: ~2x faster than shared memory approach for small blocks
 */
static __device__ __forceinline__ float warp_reduce_sum(float val) {
    unsigned mask = 0xffffffff;
    for (int offset = warpSize / 2; offset > 0; offset /= 2) {
        val += __shfl_down_sync(mask, val, offset);
    }
    return val;
}

__global__ void vector_sum_warp_shuffle(const float* input, float* output, int N) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    int lane = threadIdx.x % warpSize;
    int warpId = threadIdx.x / warpSize;

    // Each thread loads one element
    float val = (tid < N) ? input[tid] : 0.0f;

    // Warp-level reduction
    val = warp_reduce_sum(val);

    // Only lane 0 of each warp writes to shared memory
    __shared__ float warp_sums[32];  // Max 32 warps per block
    if (lane == 0) {
        warp_sums[warpId] = val;
    }
    __syncthreads();

    // First warp reduces the warp sums
    if (warpId == 0) {
        val = (lane < blockDim.x / warpSize) ? warp_sums[lane] : 0.0f;
        val = warp_reduce_sum(val);

        // Lane 0 writes final block result
        if (lane == 0) {
            atomicAdd(output, val);
        }
    }
}

// =============================================================================
// Atomic Operations for Histogram (Vector Indexing)
// =============================================================================

/**
 * Demonstrates atomic histogram using shared memory optimization
 * Shows privatization strategy to reduce atomic contention
 */
__global__ void vector_histogram_atomic(const int* input, int* histogram,
                                        int N, int num_bins) {
    extern __shared__ int shared_hist[];

    int tid = threadIdx.x;
    int gid = blockIdx.x * blockDim.x + threadIdx.x;

    // Initialize shared histogram
    for (int bin = tid; bin < num_bins; bin += blockDim.x) {
        shared_hist[bin] = 0;
    }
    __syncthreads();

    // Accumulate in shared memory (reduced contention)
    if (gid < N) {
        int bin = input[gid] % num_bins;
        atomicAdd(&shared_hist[bin], 1);
    }
    __syncthreads();

    // Write back to global memory
    for (int bin = tid; bin < num_bins; bin += blockDim.x) {
        atomicAdd(&histogram[bin], shared_hist[bin]);
    }
}

// =============================================================================
// Cooperative Groups for Flexible Vector Operations
// =============================================================================

/**
 * Vector dot product using cooperative groups
 * Demonstrates flexible thread grouping and modern sync patterns
 */
__global__ void vector_dot_coop_groups(const float* a, const float* b,
                                       float* result, int N) {
    // Create thread block and tile groups
    cg::thread_block block = cg::this_thread_block();
    cg::thread_block_tile<32> tile32 = cg::tiled_partition<32>(block);

    int tid = block.group_index().x * block.size() + block.thread_rank();

    // Compute partial dot product
    float partial_sum = 0.0f;
    for (int i = tid; i < N; i += gridDim.x * blockDim.x) {
        partial_sum += a[i] * b[i];
    }

    // Tile-level reduction using warp shuffle (CUDA 13 compatible)
    // Manual reduction since cg::reduce is not available in CUDA 13
    for (int offset = tile32.size() / 2; offset > 0; offset /= 2) {
        partial_sum += tile32.shfl_down(partial_sum, offset);
    }

    // Accumulate tile results
    __shared__ float tile_results[32];
    if (tile32.thread_rank() == 0) {
        tile_results[tile32.meta_group_rank()] = partial_sum;
    }
    block.sync();

    // Final reduction by first tile
    if (tile32.meta_group_rank() == 0) {
        int num_tiles = (block.size() + 31) / 32;
        partial_sum = (tile32.thread_rank() < num_tiles) ?
                      tile_results[tile32.thread_rank()] : 0.0f;
        // Manual reduction since cg::reduce is not available in CUDA 13
        for (int offset = tile32.size() / 2; offset > 0; offset /= 2) {
            partial_sum += tile32.shfl_down(partial_sum, offset);
        }

        if (tile32.thread_rank() == 0) {
            atomicAdd(result, partial_sum);
        }
    }
}

// =============================================================================
// Memory Fences for Producer-Consumer Pattern
// =============================================================================

__device__ volatile int segment_ready[256];  // Flags for segment completion

/**
 * Producer kernel: processes and signals completion
 */
__global__ void vector_process_producer(const float* input, float* intermediate,
                                        int N, int segment_size) {
    int segment_id = blockIdx.x;
    int tid = threadIdx.x;
    int start = segment_id * segment_size;

    // Process segment
    for (int i = tid; i < segment_size && start + i < N; i += blockDim.x) {
        intermediate[start + i] = input[start + i] * input[start + i];
    }

    // Ensure writes are visible
    __threadfence();

    // Signal completion
    if (tid == 0) {
        atomicExch((int*)&segment_ready[segment_id], 1);
    }
}

/**
 * Consumer kernel: waits for producer and consumes data
 */
__global__ void vector_process_consumer(const float* intermediate, float* output,
                                        int N, int segment_size) {
    int segment_id = blockIdx.x;
    int tid = threadIdx.x;
    int start = segment_id * segment_size;

    // Wait for producer
    if (tid == 0) {
        while (atomicAdd((int*)&segment_ready[segment_id], 0) == 0);
    }
    __syncthreads();

    // Ensure we see producer's data
    __threadfence();

    // Consume and process
    for (int i = tid; i < segment_size && start + i < N; i += blockDim.x) {
        output[start + i] = sqrtf(intermediate[start + i]);
    }
}

// =============================================================================
// Spinlock for Critical Section
// =============================================================================

/**
 * Demonstrates spinlock for serialized updates
 * Shows when NOT to use locks (inefficient on GPU)
 */
class DeviceSpinLock {
private:
    int* mutex;

public:
    __device__ DeviceSpinLock(int* m) : mutex(m) {}

    __device__ void lock() {
        while (atomicCAS(mutex, 0, 1) != 0);
        __threadfence();
    }

    __device__ void unlock() {
        __threadfence();
        atomicExch(mutex, 0);
    }
};

__global__ void vector_accumulate_locked(const float* input, float* output,
                                         int* mutex, int N) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;

    if (tid < N) {
        DeviceSpinLock lock(mutex);

        // Critical section - inefficient on GPU!
        // Better to use atomicAdd directly
        lock.lock();
        *output += input[tid];
        lock.unlock();
    }
}

// =============================================================================
// Lock-Free Vector Operations
// =============================================================================

/**
 * Lock-free vector maximum using compare-and-swap
 * Demonstrates custom atomic operations
 */
static __device__ __forceinline__ float atomicMaxFloat(float* address, float val) {
    int* address_as_int = (int*)address;
    int old = *address_as_int, assumed;

    while (val > __int_as_float(old)) {
        assumed = old;
        old = atomicCAS(address_as_int, assumed, __float_as_int(val));
        if (old == assumed) break;
    }

    return __int_as_float(old);
}

__global__ void vector_max_lockfree(const float* input, float* max_val, int N) {
    extern __shared__ float shared_max[];

    int tid = threadIdx.x;
    int gid = blockIdx.x * blockDim.x + threadIdx.x;

    // Initialize shared memory
    shared_max[tid] = -FLT_MAX;
    __syncthreads();

    // Find local maximum using lock-free atomic
    if (gid < N) {
        atomicMaxFloat(&shared_max[tid], input[gid]);
    }
    __syncthreads();

    // Block-level reduction
    for (int stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (tid < stride) {
            atomicMaxFloat(&shared_max[tid], shared_max[tid + stride]);
        }
        __syncthreads();
    }

    // Write block result
    if (tid == 0) {
        atomicMaxFloat(max_val, shared_max[0]);
    }
}

// =============================================================================
// Warp Vote Functions for Convergence Detection
// =============================================================================

/**
 * Iterative vector refinement with convergence detection
 * Uses __all_sync for early termination
 */
__global__ void vector_refine_iterative(float* data, int N, float tolerance,
                                        int max_iterations) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;

    if (tid >= N) return;

    float value = data[tid];
    bool converged = false;

    for (int iter = 0; iter < max_iterations; iter++) {
        float old_value = value;

        // Some iterative refinement (example: moving average)
        float left = (tid > 0) ? data[tid - 1] : value;
        float right = (tid < N - 1) ? data[tid + 1] : value;
        value = (left + value + right) / 3.0f;

        // Check local convergence
        converged = (fabsf(value - old_value) < tolerance);

        // Check if entire warp converged using warp vote
        unsigned mask = 0xffffffff;
        if (__all_sync(mask, converged)) {
            // All threads in warp converged - can exit early
            break;
        }

        // Update shared data
        __threadfence_block();
        data[tid] = value;
        __syncthreads();
    }

    data[tid] = value;
}

// =============================================================================
// Warp Ballot for Efficient Predicate Counting
// =============================================================================

/**
 * Count elements matching predicate using warp ballot
 * More efficient than atomic counting
 */
__global__ void vector_count_predicate(const float* input, int* count,
                                       int N, float threshold) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;

    // Evaluate predicate
    bool matches = (tid < N) && (input[tid] > threshold);

    // Use warp ballot to count matches in warp
    unsigned mask = 0xffffffff;
    unsigned ballot = __ballot_sync(mask, matches);

    // Lane 0 of each warp adds count
    int lane = tid % warpSize;
    if (lane == 0) {
        int warp_count = __popc(ballot);  // Population count
        atomicAdd(count, warp_count);
    }
}

// =============================================================================
// Helper: Reset synchronization flags
// =============================================================================

__global__ void reset_segment_flags(int num_segments) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < num_segments) {
        segment_ready[idx] = 0;
    }
}
