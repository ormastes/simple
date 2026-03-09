/**
 * Matrix Multiplication with Progressive Memory Coalescing Optimizations
 *
 * This file demonstrates the evolution from basic to highly optimized matrix
 * multiplication, focusing specifically on memory coalescing and bank conflicts.
 *
 * Optimization Levels:
 * 1. Naive - No optimizations (poor coalescing, no shared memory)
 * 2. Tiled - Shared memory with basic padding (from module 23)
 * 3. Coalesced Global - Optimized global memory access patterns
 * 4. Vectorized - Using vector loads (float4) for 16-byte transactions
 * 5. Prefetch - Double buffering with software prefetching
 *
 * Module 24 Focus: Memory coalescing and access pattern optimization
 */

#include <cuda_runtime.h>

// ============================================================================
// Level 1: Naive Implementation (Poor Coalescing)
// ============================================================================

/**
 * Naive matrix multiplication - demonstrates poor memory access
 *
 * Memory Access Issues:
 * - Matrix B accessed column-wise (non-coalesced)
 * - Each thread accesses strided memory in B: B[k * N + col]
 * - No data reuse across threads in a warp
 * - Every access to B requires separate transaction
 *
 * Performance: ~50-100 GFLOPS (extremely poor)
 */
__global__ void matmul_naive(const float* __restrict__ A,
                              const float* __restrict__ B,
                              float* __restrict__ C,
                              int M, int N, int K) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < M && col < N) {
        float sum = 0.0f;
        for (int k = 0; k < K; k++) {
            // A: coalesced (row-major, consecutive columns)
            // B: non-coalesced (column access, stride = N)
            sum += A[row * K + k] * B[k * N + col];
        }
        C[row * N + col] = sum;
    }
}

// ============================================================================
// Level 2: Tiled with Bank Conflict Padding (From Module 23)
// ============================================================================

/**
 * Tiled matrix multiplication with bank conflict padding
 *
 * Improvements from Naive:
 * - Shared memory for data reuse
 * - Bank conflict padding [TILE_SIZE][TILE_SIZE + 1]
 * - Coalesced loads from global memory
 *
 * Memory Access Pattern:
 * - Load A: thread (tx, ty) loads A[ty][tx] - coalesced
 * - Load B: thread (tx, ty) loads B[ty][tx] - coalesced
 * - Compute: Access shared memory with padding
 * - Store C: Coalesced write
 *
 * Performance: ~1-2 TFLOPS (20-40x faster than naive)
 */
template<int TILE_SIZE>
__global__ void matmul_tiled_padded(const float* __restrict__ A,
                                     const float* __restrict__ B,
                                     float* __restrict__ C,
                                     int M, int N, int K) {
    // Padded shared memory to avoid bank conflicts
    __shared__ float As[TILE_SIZE][TILE_SIZE + 1];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE + 1];

    int bx = blockIdx.x, by = blockIdx.y;
    int tx = threadIdx.x, ty = threadIdx.y;

    int row = by * TILE_SIZE + ty;
    int col = bx * TILE_SIZE + tx;

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

        // Compute using shared memory
        #pragma unroll
        for (int k = 0; k < TILE_SIZE; k++) {
            sum += As[ty][k] * Bs[k][tx];
        }

        __syncthreads();
    }

    // Store result (coalesced)
    if (row < M && col < N) {
        C[row * N + col] = sum;
    }
}

// ============================================================================
// Level 3: Vectorized Global Memory Access
// ============================================================================

/**
 * Matrix multiplication using vectorized loads
 *
 * Key Optimization:
 * - Load 4 elements at once using float4
 * - 16-byte transactions instead of 4-byte
 * - Better memory bandwidth utilization
 * - Requires N and K to be multiples of 4
 *
 * Memory Access:
 * - Load from A: 4 consecutive elements (float4)
 * - Load from B: 4 consecutive elements (float4)
 * - Improved memory bandwidth: ~1.5x better than scalar
 *
 * Performance: ~2-3 TFLOPS (1.5x faster than tiled)
 */
template<int TILE_SIZE>
__global__ void matmul_vectorized(const float* __restrict__ A,
                                   const float* __restrict__ B,
                                   float* __restrict__ C,
                                   int M, int N, int K) {
    static_assert(TILE_SIZE % 4 == 0, "TILE_SIZE must be multiple of 4");

    __shared__ float As[TILE_SIZE][TILE_SIZE + 1];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE + 1];

    int bx = blockIdx.x, by = blockIdx.y;
    int tx = threadIdx.x, ty = threadIdx.y;

    int row = by * TILE_SIZE + ty;
    int col = bx * TILE_SIZE + tx;

    float sum = 0.0f;

    for (int t = 0; t < K / TILE_SIZE; t++) {
        // Vectorized load from A (load 4 elements at once)
        if (row < M && tx % 4 == 0 && (t * TILE_SIZE + tx + 3) < K) {
            float4 a_vec = *reinterpret_cast<const float4*>(
                &A[row * K + t * TILE_SIZE + tx]);
            As[ty][tx + 0] = a_vec.x;
            As[ty][tx + 1] = a_vec.y;
            As[ty][tx + 2] = a_vec.z;
            As[ty][tx + 3] = a_vec.w;
        } else if (row < M) {
            // Fallback for boundary elements
            for (int i = 0; i < 4 && (t * TILE_SIZE + tx + i) < K; i++) {
                As[ty][tx + i] = A[row * K + t * TILE_SIZE + tx + i];
            }
        }

        // Vectorized load from B
        if ((t * TILE_SIZE + ty) < K && col < N && tx % 4 == 0) {
            float4 b_vec = *reinterpret_cast<const float4*>(
                &B[(t * TILE_SIZE + ty) * N + bx * TILE_SIZE + tx]);
            Bs[ty][tx + 0] = b_vec.x;
            Bs[ty][tx + 1] = b_vec.y;
            Bs[ty][tx + 2] = b_vec.z;
            Bs[ty][tx + 3] = b_vec.w;
        }

        __syncthreads();

        #pragma unroll
        for (int k = 0; k < TILE_SIZE; k++) {
            sum += As[ty][k] * Bs[k][tx];
        }

        __syncthreads();
    }

    if (row < M && col < N) {
        C[row * N + col] = sum;
    }
}

// ============================================================================
// Level 4: Prefetch with Double Buffering
// ============================================================================

/**
 * Matrix multiplication with software prefetching
 *
 * Advanced Optimization:
 * - Double buffering in shared memory
 * - Overlap next tile load with current tile compute
 * - Hides memory latency behind computation
 *
 * Memory Pattern:
 * - Load tile N+1 while computing tile N
 * - Reduces stalls waiting for memory
 * - Better pipeline utilization
 *
 * Performance: ~3-4 TFLOPS (best achievable without Tensor Cores)
 */
template<int TILE_SIZE>
__global__ void matmul_prefetch_double_buffer(const float* __restrict__ A,
                                               const float* __restrict__ B,
                                               float* __restrict__ C,
                                               int M, int N, int K) {
    // Double-buffered shared memory
    __shared__ float As[2][TILE_SIZE][TILE_SIZE + 1];
    __shared__ float Bs[2][TILE_SIZE][TILE_SIZE + 1];

    int bx = blockIdx.x, by = blockIdx.y;
    int tx = threadIdx.x, ty = threadIdx.y;

    int row = by * TILE_SIZE + ty;
    int col = bx * TILE_SIZE + tx;

    float sum = 0.0f;

    int num_tiles = (K + TILE_SIZE - 1) / TILE_SIZE;

    // Prefetch first tile (buffer 0)
    int t = 0;
    int buffer = 0;

    if (row < M && (t * TILE_SIZE + tx) < K) {
        As[buffer][ty][tx] = A[row * K + t * TILE_SIZE + tx];
    } else {
        As[buffer][ty][tx] = 0.0f;
    }

    if ((t * TILE_SIZE + ty) < K && col < N) {
        Bs[buffer][ty][tx] = B[(t * TILE_SIZE + ty) * N + col];
    } else {
        Bs[buffer][ty][tx] = 0.0f;
    }

    __syncthreads();

    // Main loop with double buffering
    for (t = 1; t < num_tiles; t++) {
        int next_buffer = 1 - buffer;

        // Prefetch next tile while computing current
        if (row < M && (t * TILE_SIZE + tx) < K) {
            As[next_buffer][ty][tx] = A[row * K + t * TILE_SIZE + tx];
        } else {
            As[next_buffer][ty][tx] = 0.0f;
        }

        if ((t * TILE_SIZE + ty) < K && col < N) {
            Bs[next_buffer][ty][tx] = B[(t * TILE_SIZE + ty) * N + col];
        } else {
            Bs[next_buffer][ty][tx] = 0.0f;
        }

        // Compute current tile
        #pragma unroll
        for (int k = 0; k < TILE_SIZE; k++) {
            sum += As[buffer][ty][k] * Bs[buffer][k][tx];
        }

        buffer = next_buffer;
        __syncthreads();
    }

    // Compute last tile
    #pragma unroll
    for (int k = 0; k < TILE_SIZE; k++) {
        sum += As[buffer][ty][k] * Bs[buffer][k][tx];
    }

    // Store result (coalesced write)
    if (row < M && col < N) {
        C[row * N + col] = sum;
    }
}

// ============================================================================
// Level 5: Optimized for Memory Coalescing (Module 24 Focus)
// ============================================================================

/**
 * Matrix multiplication optimized specifically for coalescing
 *
 * Module 24 Improvements:
 * 1. Perfect coalescing on all global loads/stores
 * 2. Bank conflict elimination via padding
 * 3. Alignment hints for compiler
 * 4. Memory access pattern documentation
 *
 * Coalescing Analysis:
 * - Load A: Thread (ty, tx) loads A[row][t*TILE + tx]
 *   → Consecutive threads (tx: 0-31) load consecutive addresses ✓
 * - Load B: Thread (ty, tx) loads B[t*TILE + ty][col]
 *   → Consecutive threads (tx: 0-31) load consecutive addresses ✓
 * - Store C: Thread (ty, tx) stores C[row][col]
 *   → Consecutive threads (tx: 0-31) store consecutive addresses ✓
 *
 * Bank Conflict Analysis:
 * - As[ty][tx]: Linear indexing, no conflicts ✓
 * - Bs[ty][tx]: Linear indexing, no conflicts ✓
 * - Compute As[ty][k] * Bs[k][tx]: +1 padding eliminates conflicts ✓
 */
template<int TILE_SIZE>
__global__ void matmul_coalescing_optimized(const float* __restrict__ A,
                                             const float* __restrict__ B,
                                             float* __restrict__ C,
                                             int M, int N, int K) {
    // Bank conflict padding for transpose access
    __shared__ float As[TILE_SIZE][TILE_SIZE + 1];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE + 1];

    const int bx = blockIdx.x;
    const int by = blockIdx.y;
    const int tx = threadIdx.x;
    const int ty = threadIdx.y;

    // Global indices
    const int row = by * TILE_SIZE + ty;
    const int col = bx * TILE_SIZE + tx;

    float sum = 0.0f;

    const int num_tiles = (K + TILE_SIZE - 1) / TILE_SIZE;

    for (int t = 0; t < num_tiles; t++) {
        // Coalesced load from A
        // Thread block reads consecutive elements:
        // warp 0: A[row][t*TILE + 0..31], warp 1: A[row][t*TILE + 32..63], etc.
        const int a_col = t * TILE_SIZE + tx;
        if (row < M && a_col < K) {
            As[ty][tx] = __ldg(&A[row * K + a_col]);
        } else {
            As[ty][tx] = 0.0f;
        }

        // Coalesced load from B
        // Thread block reads consecutive elements:
        // warp 0: B[t*TILE + ty][col], consecutive in col dimension
        const int b_row = t * TILE_SIZE + ty;
        if (b_row < K && col < N) {
            Bs[ty][tx] = __ldg(&B[b_row * N + col]);
        } else {
            Bs[ty][tx] = 0.0f;
        }

        __syncthreads();

        // Compute using shared memory
        // No bank conflicts due to +1 padding
        #pragma unroll
        for (int k = 0; k < TILE_SIZE; k++) {
            sum += As[ty][k] * Bs[k][tx];
        }

        __syncthreads();
    }

    // Coalesced write to C
    // Consecutive threads write consecutive addresses
    if (row < M && col < N) {
        C[row * N + col] = sum;
    }
}
