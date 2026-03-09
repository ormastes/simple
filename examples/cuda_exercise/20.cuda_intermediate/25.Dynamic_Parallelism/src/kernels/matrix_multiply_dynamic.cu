/**
 * Matrix Multiplication with Dynamic Parallelism
 *
 * This file enhances Module 24's matrix multiplication kernels by adding
 * dynamic parallelism capabilities for adaptive tiling and recursive subdivision.
 *
 * Dynamic Parallelism Features:
 * 1. Adaptive Tiling - Parent kernel analyzes workload and launches appropriately sized children
 * 2. Recursive Subdivision - Large matrices subdivided into smaller chunks dynamically
 * 3. Load-Balanced Processing - Dynamic workload distribution based on matrix dimensions
 *
 * Module 25 Focus: Dynamic kernel launches from within kernels
 */

#include <cuda_runtime.h>
#include <cuda_device_runtime_api.h>

// Maximum recursion depth for dynamic subdivision
#define MAX_RECURSION_DEPTH 3

// Threshold for launching child kernels (matrix dimension)
#define SUBDIVISION_THRESHOLD 512

// ============================================================================
// Base Tiled Kernel (from Module 24, optimized version)
// ============================================================================

/**
 * Optimized tiled matrix multiplication (leaf kernel)
 * This is the actual computation kernel launched by dynamic parent
 */
template<int TILE_SIZE>
__global__ void matmul_tiled_leaf(const float* __restrict__ A,
                                   const float* __restrict__ B,
                                   float* __restrict__ C,
                                   int M, int N, int K,
                                   int row_offset, int col_offset) {
    // Padded shared memory to avoid bank conflicts
    __shared__ float As[TILE_SIZE][TILE_SIZE + 1];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE + 1];

    int tx = threadIdx.x, ty = threadIdx.y;
    int row = row_offset + blockIdx.y * TILE_SIZE + ty;
    int col = col_offset + blockIdx.x * TILE_SIZE + tx;

    float sum = 0.0f;

    // Loop over tiles
    for (int t = 0; t < (K + TILE_SIZE - 1) / TILE_SIZE; t++) {
        // Load A tile (coalesced)
        if (row < M && (t * TILE_SIZE + tx) < K) {
            As[ty][tx] = A[row * K + t * TILE_SIZE + tx];
        } else {
            As[ty][tx] = 0.0f;
        }

        // Load B tile (coalesced)
        if ((t * TILE_SIZE + ty) < K && col < N) {
            Bs[ty][tx] = B[(t * TILE_SIZE + ty) * N + col];
        } else {
            Bs[ty][tx] = 0.0f;
        }

        __syncthreads();

        // Compute partial sum
        #pragma unroll
        for (int k = 0; k < TILE_SIZE; k++) {
            sum += As[ty][k] * Bs[k][tx];
        }

        __syncthreads();
    }

    // Write result
    if (row < M && col < N) {
        C[row * N + col] = sum;
    }
}

// ============================================================================
// Dynamic Parallelism: Adaptive Matrix Multiplication
// ============================================================================

/**
 * Adaptive matrix multiplication with dynamic tiling
 *
 * Parent kernel analyzes matrix dimensions and adaptively launches
 * child kernels with optimal grid configurations.
 *
 * Strategy:
 * - Small matrices (< 512x512): Launch single kernel
 * - Medium matrices (512-2048): Launch 2x2 grid of child kernels
 * - Large matrices (> 2048): Recursive subdivision
 */
template<int TILE_SIZE>
__global__ void matmul_adaptive_parent(const float* A,
                                        const float* B,
                                        float* C,
                                        int M, int N, int K,
                                        int depth) {
    // Only thread 0 in block 0 decides strategy
    if (threadIdx.x != 0 || threadIdx.y != 0 || blockIdx.x != 0 || blockIdx.y != 0) return;

    // Base case: Small enough to compute directly
    if (M <= SUBDIVISION_THRESHOLD && N <= SUBDIVISION_THRESHOLD || depth >= MAX_RECURSION_DEPTH) {
        dim3 block(TILE_SIZE, TILE_SIZE);
        dim3 grid((N + TILE_SIZE - 1) / TILE_SIZE, (M + TILE_SIZE - 1) / TILE_SIZE);

        matmul_tiled_leaf<TILE_SIZE><<<grid, block>>>(A, B, C, M, N, K, 0, 0);
        return;
    }

    // Recursive case: Subdivide matrix into quadrants
    int M_half = M / 2;
    int N_half = N / 2;

    // Launch 4 child kernels for 4 quadrants
    // Top-left quadrant
    matmul_adaptive_parent<TILE_SIZE><<<1, 1>>>(A, B, C, M_half, N_half, K, depth + 1);

    // Top-right quadrant
    matmul_adaptive_parent<TILE_SIZE><<<1, 1>>>(A, B + N_half, C + N_half, M_half, N - N_half, K, depth + 1);

    // Bottom-left quadrant
    matmul_adaptive_parent<TILE_SIZE><<<1, 1>>>(A + M_half * K, B, C + M_half * N, M - M_half, N_half, K, depth + 1);

    // Bottom-right quadrant
    matmul_adaptive_parent<TILE_SIZE><<<1, 1>>>(A + M_half * K, B + N_half, C + M_half * N + N_half, M - M_half, N - N_half, K, depth + 1);
}

// ============================================================================
// Dynamic Parallelism: Row-Based Dynamic Workload Distribution
// ============================================================================

/**
 * Child kernel that processes a single row of output matrix
 */
template<int BLOCK_SIZE>
__global__ void matmul_row_kernel(const float* A,
                                   const float* B,
                                   float* C,
                                   int row, int N, int K) {
    int col = blockIdx.x * BLOCK_SIZE + threadIdx.x;

    if (col < N) {
        float sum = 0.0f;
        for (int k = 0; k < K; k++) {
            sum += A[row * K + k] * B[k * N + col];
        }
        C[row * N + col] = sum;
    }
}

/**
 * Parent kernel that dynamically distributes rows to child kernels
 *
 * Each parent thread is responsible for one or more output rows.
 * Parent analyzes row workload and launches appropriate child kernel.
 */
template<int BLOCK_SIZE>
__global__ void matmul_row_dynamic(const float* A,
                                    const float* B,
                                    float* C,
                                    int M, int N, int K) {
    int row = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < M) {
        // Launch child kernel for this row
        int blocks = (N + BLOCK_SIZE - 1) / BLOCK_SIZE;
        matmul_row_kernel<BLOCK_SIZE><<<blocks, BLOCK_SIZE>>>(A, B, C, row, N, K);
    }
}

// ============================================================================
// Dynamic Parallelism: Hybrid Approach
// ============================================================================

/**
 * Hybrid kernel combining static and dynamic strategies
 *
 * - First level: Static grid of blocks (parent kernels)
 * - Second level: Each block dynamically launches children based on workload
 *
 * Advantages:
 * - Reduces CPU-GPU synchronization
 * - Adapts to non-uniform workloads
 * - Better GPU utilization
 */
template<int TILE_SIZE>
__global__ void matmul_hybrid_parent(const float* A,
                                      const float* B,
                                      float* C,
                                      int M, int N, int K,
                                      int tiles_per_block) {
    // Each block is responsible for multiple tiles
    int block_tile_row = blockIdx.y;
    int block_tile_col = blockIdx.x;

    // Calculate this block's responsibility
    int row_start = block_tile_row * tiles_per_block * TILE_SIZE;
    int col_start = block_tile_col * tiles_per_block * TILE_SIZE;

    // Only first thread in block launches children
    if (threadIdx.x == 0 && threadIdx.y == 0) {
        // Launch child kernels for tiles in this block's region
        for (int tr = 0; tr < tiles_per_block; tr++) {
            for (int tc = 0; tc < tiles_per_block; tc++) {
                int row_offset = row_start + tr * TILE_SIZE;
                int col_offset = col_start + tc * TILE_SIZE;

                // Check if this tile is within bounds
                if (row_offset < M && col_offset < N) {
                    dim3 block(TILE_SIZE, TILE_SIZE);
                    dim3 grid(1, 1);

                    matmul_tiled_leaf<TILE_SIZE><<<grid, block>>>(
                        A, B, C, M, N, K, row_offset, col_offset);
                }
            }
        }
    }
}

// ============================================================================
// Dynamic Parallelism: Block-Level Adaptive Strategy
// ============================================================================

/**
 * Each block analyzes its workload and decides whether to:
 * 1. Compute directly (small workload)
 * 2. Launch child kernels (medium workload)
 * 3. Further subdivide (large workload)
 */
template<int TILE_SIZE>
__global__ void matmul_block_adaptive(const float* A,
                                       const float* B,
                                       float* C,
                                       int M, int N, int K,
                                       int block_M, int block_N,
                                       int depth) {
    // Calculate this block's region
    int row_start = blockIdx.y * block_M;
    int col_start = blockIdx.x * block_N;
    int row_end = min(row_start + block_M, M);
    int col_end = min(col_start + block_N, N);

    int region_M = row_end - row_start;
    int region_N = col_end - col_start;

    // Only first thread makes decision
    if (threadIdx.x == 0 && threadIdx.y == 0) {
        // Small region: compute directly with this block's threads
        if (region_M <= TILE_SIZE && region_N <= TILE_SIZE) {
            // Compute using block's threads
            dim3 block(TILE_SIZE, TILE_SIZE);
            matmul_tiled_leaf<TILE_SIZE><<<1, block>>>(
                A, B, C, M, N, K, row_start, col_start);
        }
        // Medium region: launch grid of child kernels
        else if (depth < MAX_RECURSION_DEPTH) {
            dim3 block(TILE_SIZE, TILE_SIZE);
            dim3 grid((region_N + TILE_SIZE - 1) / TILE_SIZE,
                     (region_M + TILE_SIZE - 1) / TILE_SIZE);

            matmul_tiled_leaf<TILE_SIZE><<<grid, block>>>(
                A, B, C, M, N, K, row_start, col_start);
        }
    }
}
