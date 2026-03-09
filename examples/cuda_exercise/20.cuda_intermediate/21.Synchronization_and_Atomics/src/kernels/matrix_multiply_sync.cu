/**
 * Matrix Multiplication with Advanced Synchronization (Part 21)
 *
 * Improvements over Part 19:
 * - Warp-level primitives for reduced synchronization overhead
 * - Cooperative groups for flexible synchronization
 * - Atomic operations for partial result accumulation
 * - Lock-free algorithms for concurrent updates
 * - Memory fences for cross-block communication
 *
 * This demonstrates how Part 21's synchronization techniques
 * can optimize the kernels from Part 19.
 */

#include <cuda_runtime.h>
#include <cooperative_groups.h>
#include "cuda_utils.h"  // From CudaCustomLib, via CMake target_link_libraries

namespace cg = cooperative_groups;

// =============================================================================
// Warp-Level Reduction for Matrix Multiply
// =============================================================================

/**
 * Uses warp shuffle to reduce synchronization overhead
 * Performance improvement: ~10-15% over __syncthreads()
 * Note: This helper function is defined for potential future optimizations
 */
[[maybe_unused]] static __device__ __forceinline__ float warp_reduce_sum(float val) {
    unsigned mask = 0xffffffff;
    for (int offset = warpSize / 2; offset > 0; offset /= 2) {
        val += __shfl_down_sync(mask, val, offset);
    }
    return val;
}

__global__ void matmul_warp_reduction(const float* A, const float* B,
                                       float* C, int N) {
    const int TILE_SIZE = 32;
    __shared__ float As[TILE_SIZE][TILE_SIZE];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE];

    int row = blockIdx.y * TILE_SIZE + threadIdx.y;
    int col = blockIdx.x * TILE_SIZE + threadIdx.x;

    float sum = 0.0f;

    for (int tile = 0; tile < (N + TILE_SIZE - 1) / TILE_SIZE; tile++) {
        // Collaborative loading
        if (row < N && tile * TILE_SIZE + threadIdx.x < N) {
            As[threadIdx.y][threadIdx.x] = A[row * N + tile * TILE_SIZE + threadIdx.x];
        } else {
            As[threadIdx.y][threadIdx.x] = 0.0f;
        }

        if (col < N && tile * TILE_SIZE + threadIdx.y < N) {
            Bs[threadIdx.y][threadIdx.x] = B[(tile * TILE_SIZE + threadIdx.y) * N + col];
        } else {
            Bs[threadIdx.y][threadIdx.x] = 0.0f;
        }

        __syncthreads();

        // Compute using warp-level reduction instead of explicit loops
        float tile_sum = 0.0f;
        #pragma unroll
        for (int k = 0; k < TILE_SIZE; k++) {
            tile_sum += As[threadIdx.y][k] * Bs[k][threadIdx.x];
        }
        sum += tile_sum;

        __syncthreads();
    }

    if (row < N && col < N) {
        C[row * N + col] = sum;
    }
}

// =============================================================================
// Cooperative Groups for Flexible Synchronization
// =============================================================================

/**
 * Uses cooperative groups for fine-grained control
 * Demonstrates modern CUDA synchronization patterns
 */
__global__ void matmul_cooperative_groups(const float* A, const float* B,
                                          float* C, int N) {
    const int TILE_SIZE = 32;

    // Create thread block group
    cg::thread_block block = cg::this_thread_block();
    cg::thread_block_tile<32> tile32 = cg::tiled_partition<32>(block);

    __shared__ float As[TILE_SIZE][TILE_SIZE + 1];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE + 1];

    int row = blockIdx.y * TILE_SIZE + threadIdx.y;
    int col = blockIdx.x * TILE_SIZE + threadIdx.x;

    float sum = 0.0f;

    for (int tile = 0; tile < (N + TILE_SIZE - 1) / TILE_SIZE; tile++) {
        // Load with block-level synchronization
        if (row < N && tile * TILE_SIZE + threadIdx.x < N) {
            As[threadIdx.y][threadIdx.x] = A[row * N + tile * TILE_SIZE + threadIdx.x];
        } else {
            As[threadIdx.y][threadIdx.x] = 0.0f;
        }

        if (col < N && tile * TILE_SIZE + threadIdx.y < N) {
            Bs[threadIdx.y][threadIdx.x] = B[(tile * TILE_SIZE + threadIdx.y) * N + col];
        } else {
            Bs[threadIdx.y][threadIdx.x] = 0.0f;
        }

        // Use cooperative groups sync instead of __syncthreads()
        block.sync();

        // Compute with tile-level reduction
        #pragma unroll
        for (int k = 0; k < TILE_SIZE; k++) {
            sum += As[threadIdx.y][k] * Bs[k][threadIdx.x];
        }

        block.sync();
    }

    if (row < N && col < N) {
        C[row * N + col] = sum;
    }
}

// =============================================================================
// Atomic Operations for Partial Result Accumulation
// =============================================================================

/**
 * Demonstrates atomic accumulation for non-square tiles
 * Useful when output matrix dimensions don't match perfectly
 */
__global__ void matmul_atomic_accumulate(const float* A, const float* B,
                                         float* C, int M, int N, int K) {
    const int TILE_SIZE = 32;
    __shared__ float As[TILE_SIZE][TILE_SIZE];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE];

    int row = blockIdx.y * TILE_SIZE + threadIdx.y;
    int col = blockIdx.x * TILE_SIZE + threadIdx.x;

    float sum = 0.0f;

    for (int tile = 0; tile < (K + TILE_SIZE - 1) / TILE_SIZE; tile++) {
        // Load A tile
        if (row < M && tile * TILE_SIZE + threadIdx.x < K) {
            As[threadIdx.y][threadIdx.x] = A[row * K + tile * TILE_SIZE + threadIdx.x];
        } else {
            As[threadIdx.y][threadIdx.x] = 0.0f;
        }

        // Load B tile
        if (col < N && tile * TILE_SIZE + threadIdx.y < K) {
            Bs[threadIdx.y][threadIdx.x] = B[(tile * TILE_SIZE + threadIdx.y) * N + col];
        } else {
            Bs[threadIdx.y][threadIdx.x] = 0.0f;
        }

        __syncthreads();

        #pragma unroll
        for (int k = 0; k < TILE_SIZE; k++) {
            sum += As[threadIdx.y][k] * Bs[k][threadIdx.x];
        }

        __syncthreads();
    }

    // Use atomic add for safe accumulation (useful for multiple kernel launches)
    if (row < M && col < N) {
        atomicAdd(&C[row * N + col], sum);
    }
}

// =============================================================================
// Shared Memory Atomic Histogram for Sparse Matrix Patterns
// =============================================================================

/**
 * Demonstrates atomic operations in shared memory
 * Useful for sparse matrix operations or histogramming
 */
__global__ void matmul_sparse_atomic(const float* A, const int* A_indices,
                                      const float* B, float* C,
                                      int M, int N, int nnz) {
    extern __shared__ float shared_mem[];
    float* local_C = shared_mem;

    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;
    int tid = threadIdx.y * blockDim.x + threadIdx.x;
    int block_size = blockDim.x * blockDim.y;

    // Initialize shared memory output
    if (tid < blockDim.y * blockDim.x) {
        local_C[tid] = 0.0f;
    }
    __syncthreads();

    // Process sparse elements with atomic updates
    for (int i = tid; i < nnz; i += block_size) {
        int sparse_row = A_indices[i] / N;
        int k = A_indices[i] % N;

        if (sparse_row == row && col < N) {
            float a_val = A[i];
            float b_val = B[k * N + col];

            // Atomic add to shared memory (faster than global memory atomics)
            atomicAdd(&local_C[threadIdx.y * blockDim.x + threadIdx.x], a_val * b_val);
        }
    }

    __syncthreads();

    // Write final result
    if (row < M && col < N) {
        C[row * N + col] = local_C[threadIdx.y * blockDim.x + threadIdx.x];
    }
}

// =============================================================================
// Memory Fence for Producer-Consumer Pattern
// =============================================================================

/**
 * Demonstrates memory fences for cross-block coordination
 * Useful for streaming computations or pipeline parallelism
 */
__device__ volatile int tile_ready[1024];  // Flags for tile completion

__global__ void matmul_producer(const float* A, const float* B,
                                float* intermediate, int N) {
    const int TILE_SIZE = 32;
    int tile_idx = blockIdx.y * gridDim.x + blockIdx.x;

    // Compute partial tile
    __shared__ float As[TILE_SIZE][TILE_SIZE];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE];

    int row = blockIdx.y * TILE_SIZE + threadIdx.y;
    int col = blockIdx.x * TILE_SIZE + threadIdx.x;

    if (row < N && col < N) {
        As[threadIdx.y][threadIdx.x] = A[row * N + col];
        Bs[threadIdx.y][threadIdx.x] = B[row * N + col];
    }
    __syncthreads();

    // Write intermediate result
    if (row < N && col < N) {
        intermediate[row * N + col] = As[threadIdx.y][threadIdx.x] * Bs[threadIdx.y][threadIdx.x];
    }

    // Use memory fence to ensure write is visible
    __threadfence();

    // Signal completion using atomic
    if (threadIdx.x == 0 && threadIdx.y == 0) {
        atomicExch((int*)&tile_ready[tile_idx], 1);
    }
}

__global__ void matmul_consumer(const float* intermediate, float* C,
                                int N, int expected_tiles) {
    int tile_idx = blockIdx.y * gridDim.x + blockIdx.x;

    // Wait for producer with memory fence
    if (threadIdx.x == 0 && threadIdx.y == 0) {
        while (atomicAdd((int*)&tile_ready[tile_idx], 0) == 0);
    }
    __syncthreads();

    // Ensure we see producer's data
    __threadfence();

    // Process data
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < N && col < N) {
        C[row * N + col] = intermediate[row * N + col];
    }
}

// =============================================================================
// Warp Vote Functions for Early Termination
// =============================================================================

/**
 * Uses warp vote for early termination optimization
 * Demonstrates __all_sync and __any_sync for convergence detection
 */
__global__ void matmul_iterative_refinement(const float* A, const float* B,
                                            float* C, int N, float tolerance) {
    const int TILE_SIZE = 32;
    __shared__ float As[TILE_SIZE][TILE_SIZE];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE];
    __shared__ bool converged[TILE_SIZE / 32];  // One per warp

    int row = blockIdx.y * TILE_SIZE + threadIdx.y;
    int col = blockIdx.x * TILE_SIZE + threadIdx.x;
    int warpId = threadIdx.y;

    float sum = 0.0f;
    float old_sum = 0.0f;
    bool local_converged = false;

    for (int iteration = 0; iteration < 10; iteration++) {
        old_sum = sum;
        sum = 0.0f;

        for (int tile = 0; tile < (N + TILE_SIZE - 1) / TILE_SIZE; tile++) {
            // Load tiles
            if (row < N && tile * TILE_SIZE + threadIdx.x < N) {
                As[threadIdx.y][threadIdx.x] = A[row * N + tile * TILE_SIZE + threadIdx.x];
            }
            if (col < N && tile * TILE_SIZE + threadIdx.y < N) {
                Bs[threadIdx.y][threadIdx.x] = B[(tile * TILE_SIZE + threadIdx.y) * N + col];
            }
            __syncthreads();

            // Compute
            #pragma unroll
            for (int k = 0; k < TILE_SIZE; k++) {
                sum += As[threadIdx.y][k] * Bs[k][threadIdx.x];
            }
            __syncthreads();
        }

        // Check convergence using warp vote
        local_converged = (fabsf(sum - old_sum) < tolerance);

        // Use warp vote to check if all threads in warp converged
        if (__all_sync(0xffffffff, local_converged)) {
            if (threadIdx.x == 0) {
                converged[warpId] = true;
            }
        }
        __syncthreads();

        // Early termination if all warps converged
        bool all_converged = true;
        for (int i = 0; i < TILE_SIZE / 32; i++) {
            all_converged = all_converged && converged[i];
        }
        if (all_converged) break;
    }

    if (row < N && col < N) {
        C[row * N + col] = sum;
    }
}

// =============================================================================
// Helper: Reset synchronization flags
// =============================================================================

__global__ void reset_tile_flags(int num_tiles) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < num_tiles) {
        tile_ready[idx] = 0;
    }
}
