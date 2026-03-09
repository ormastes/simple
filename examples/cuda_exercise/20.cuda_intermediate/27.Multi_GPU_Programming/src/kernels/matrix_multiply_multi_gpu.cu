/**
 * Multi-GPU Matrix Multiplication (Module 27)
 *
 * This file extends Module 26's cooperative groups matrix multiplication
 * to support multi-GPU execution with the following improvements:
 *
 * Enhancements over Module 26 (Single GPU):
 * 1. Row-wise data distribution across multiple GPUs
 * 2. Peer-to-peer memory access for matrix B sharing
 * 3. Concurrent kernel execution on all GPUs
 * 4. Load balancing based on GPU capabilities
 * 5. Asynchronous transfers and overlapped computation
 *
 * Multi-GPU strategies:
 * - Data parallelism: Distribute rows of matrix A across GPUs
 * - Broadcast matrix B to all GPUs or use P2P access
 * - Independent computation with minimal synchronization
 * - Result gathering with concurrent transfers
 */

#include <cuda_runtime.h>
#include <cooperative_groups.h>

namespace cg = cooperative_groups;

// ============================================================================
// Multi-GPU Tiled Matrix Multiplication
// ============================================================================

/**
 * Multi-GPU aware tiled matrix multiplication kernel
 *
 * Each GPU processes a subset of rows from matrix A
 * - A is distributed: each GPU has its portion
 * - B is replicated: all GPUs have full copy (or use P2P)
 * - C is distributed: each GPU computes its portion
 */
template<int TILE_SIZE>
__global__ void matmul_tiled_multi_gpu(
    const float* __restrict__ A_local,   // Local portion of A on this GPU
    const float* __restrict__ B,          // Full matrix B (replicated or P2P)
    float* __restrict__ C_local,          // Local portion of C on this GPU
    int M_total,                          // Total rows in A
    int N,                                // Columns in B and C
    int K,                                // Shared dimension
    int row_offset,                       // Starting row for this GPU (unused - for API consistency)
    int M_local                           // Number of rows assigned to this GPU
) {
    cg::thread_block block = cg::this_thread_block();

    // Padded shared memory to avoid bank conflicts
    __shared__ float As[TILE_SIZE][TILE_SIZE + 1];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE + 1];

    int tx = threadIdx.x, ty = threadIdx.y;

    // Local row (within this GPU's portion) - this is the actual index into A_local
    int local_row = blockIdx.y * TILE_SIZE + ty;
    int col = blockIdx.x * TILE_SIZE + tx;

    float sum = 0.0f;

    // Bounds check for this GPU's portion
    if (local_row >= M_local) return;
    if (col >= N) return;

    // Loop over tiles
    for (int t = 0; t < (K + TILE_SIZE - 1) / TILE_SIZE; t++) {
        // Load A tile (from local portion)
        // A_local is already offset to this GPU's portion, so use local_row directly
        if (local_row < M_local && (t * TILE_SIZE + tx) < K) {
            As[ty][tx] = A_local[local_row * K + t * TILE_SIZE + tx];
        } else {
            As[ty][tx] = 0.0f;
        }

        // Load B tile (from replicated full matrix)
        if ((t * TILE_SIZE + ty) < K && col < N) {
            Bs[ty][tx] = B[(t * TILE_SIZE + ty) * N + col];
        } else {
            Bs[ty][tx] = 0.0f;
        }

        block.sync();

        // Compute partial sum
        #pragma unroll
        for (int k = 0; k < TILE_SIZE; k++) {
            sum += As[ty][k] * Bs[k][tx];
        }

        block.sync();
    }

    // Write result to local portion of C
    // C_local is also offset to this GPU's portion
    if (local_row < M_local && col < N) {
        C_local[local_row * N + col] = sum;
    }
}

// ============================================================================
// Multi-GPU with Peer-to-Peer Access for Matrix B
// ============================================================================

/**
 * Multi-GPU matmul using P2P access to avoid replicating matrix B
 *
 * Instead of replicating B on all GPUs, this version uses peer-to-peer
 * memory access to read B directly from GPU 0's memory.
 *
 * Requires: Peer access enabled between GPUs
 * Performance: Depends on P2P link bandwidth (NVLink >> PCIe)
 */
template<int TILE_SIZE>
__global__ void matmul_tiled_p2p(
    const float* __restrict__ A_local,   // Local portion of A
    const float* __restrict__ B_remote,  // B on remote GPU (accessed via P2P)
    float* __restrict__ C_local,          // Local portion of C
    int M_local,                          // Rows in local A
    int N,                                // Columns
    int K                                 // Shared dimension
) {
    cg::thread_block block = cg::this_thread_block();

    __shared__ float As[TILE_SIZE][TILE_SIZE + 1];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE + 1];

    int tx = threadIdx.x, ty = threadIdx.y;
    int local_row = blockIdx.y * TILE_SIZE + ty;
    int col = blockIdx.x * TILE_SIZE + tx;

    if (local_row >= M_local) return;

    float sum = 0.0f;

    // Loop over tiles
    for (int t = 0; t < (K + TILE_SIZE - 1) / TILE_SIZE; t++) {
        // Load A tile (local memory - fast)
        if (local_row < M_local && (t * TILE_SIZE + tx) < K) {
            As[ty][tx] = A_local[local_row * K + t * TILE_SIZE + tx];
        } else {
            As[ty][tx] = 0.0f;
        }

        // Load B tile (P2P access - bandwidth depends on interconnect)
        if ((t * TILE_SIZE + ty) < K && col < N) {
            Bs[ty][tx] = B_remote[(t * TILE_SIZE + ty) * N + col];
        } else {
            Bs[ty][tx] = 0.0f;
        }

        block.sync();

        #pragma unroll
        for (int k = 0; k < TILE_SIZE; k++) {
            sum += As[ty][k] * Bs[k][tx];
        }

        block.sync();
    }

    if (local_row < M_local && col < N) {
        C_local[local_row * N + col] = sum;
    }
}

// ============================================================================
// Multi-GPU Cooperative Groups with Warp Specialization
// ============================================================================

/**
 * Multi-GPU matmul with warp-level cooperative loading
 *
 * This version uses cooperative groups to optimize tile loading:
 * - Warp-level collaboration for coalesced memory access
 * - Better utilization of memory bandwidth
 * - Reduced shared memory bank conflicts
 */
template<int TILE_SIZE>
__global__ void matmul_warp_cooperative_multi_gpu(
    const float* __restrict__ A_local,
    const float* __restrict__ B,
    float* __restrict__ C_local,
    int M_local,
    int N,
    int K
) {
    cg::thread_block block = cg::this_thread_block();
    cg::thread_block_tile<32> warp = cg::tiled_partition<32>(block);

    __shared__ float As[TILE_SIZE][TILE_SIZE + 1];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE + 1];

    int tx = threadIdx.x, ty = threadIdx.y;
    int local_row = blockIdx.y * TILE_SIZE + ty;
    int col = blockIdx.x * TILE_SIZE + tx;

    if (local_row >= M_local) return;

    float sum = 0.0f;

    // Each warp loads tiles cooperatively
    int warp_id = (ty * TILE_SIZE + tx) / 32;
    int lane_id = warp.thread_rank();

    for (int t = 0; t < (K + TILE_SIZE - 1) / TILE_SIZE; t++) {
        // Cooperative warp loading for A
        int flat_tid = ty * TILE_SIZE + tx;
        int elements_per_tile = TILE_SIZE * TILE_SIZE;

        for (int i = flat_tid; i < elements_per_tile; i += blockDim.x * blockDim.y) {
            int tile_row = i / TILE_SIZE;
            int tile_col = i % TILE_SIZE;

            if (tile_row < M_local && (t * TILE_SIZE + tile_col) < K) {
                As[tile_row][tile_col] = A_local[tile_row * K + t * TILE_SIZE + tile_col];
            } else {
                As[tile_row][tile_col] = 0.0f;
            }
        }

        // Cooperative warp loading for B
        for (int i = flat_tid; i < elements_per_tile; i += blockDim.x * blockDim.y) {
            int tile_row = i / TILE_SIZE;
            int tile_col = i % TILE_SIZE;

            if ((t * TILE_SIZE + tile_row) < K && (blockIdx.x * TILE_SIZE + tile_col) < N) {
                Bs[tile_row][tile_col] = B[(t * TILE_SIZE + tile_row) * N +
                                           blockIdx.x * TILE_SIZE + tile_col];
            } else {
                Bs[tile_row][tile_col] = 0.0f;
            }
        }

        block.sync();

        // Compute
        #pragma unroll
        for (int k = 0; k < TILE_SIZE; k++) {
            sum += As[ty][k] * Bs[k][tx];
        }

        block.sync();
    }

    if (local_row < M_local && col < N) {
        C_local[local_row * N + col] = sum;
    }
}

// Explicit template instantiations
template __global__ void matmul_tiled_multi_gpu<16>(const float*, const float*, float*, int, int, int, int, int);
template __global__ void matmul_tiled_multi_gpu<32>(const float*, const float*, float*, int, int, int, int, int);

template __global__ void matmul_tiled_p2p<16>(const float*, const float*, float*, int, int, int);
template __global__ void matmul_tiled_p2p<32>(const float*, const float*, float*, int, int, int);

template __global__ void matmul_warp_cooperative_multi_gpu<16>(const float*, const float*, float*, int, int, int);
template __global__ void matmul_warp_cooperative_multi_gpu<32>(const float*, const float*, float*, int, int, int);
