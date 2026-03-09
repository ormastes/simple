/**
 * @file matmul_cuda.cu
 * @brief Tiled matrix multiplication kernel for PyTorch native extension
 *
 * Implements a 32x32 shared-memory tiled matrix multiplication. The kernel
 * is designed to be called from the pybind11 bindings layer via native_matmul().
 * It handles non-tile-aligned dimensions with boundary checks.
 */

#include "native_ops.h"
#include <cuda_runtime.h>

/// Tile dimension for shared-memory blocking
constexpr int TILE_DIM = 32;

/**
 * @brief Tiled matmul kernel: C[MxN] = A[MxK] * B[KxN]
 *
 * Each thread block computes a TILE_DIM x TILE_DIM output sub-matrix by
 * iterating over the K dimension in TILE_DIM-wide steps. Shared memory tiles
 * reduce global memory bandwidth by a factor of ~TILE_DIM.
 */
__global__ void native_tiled_matmul_kernel(float* __restrict__ C,
                                           const float* __restrict__ A,
                                           const float* __restrict__ B,
                                           int M, int N, int K) {
    __shared__ float sA[TILE_DIM][TILE_DIM];
    __shared__ float sB[TILE_DIM][TILE_DIM];

    int row = blockIdx.y * TILE_DIM + threadIdx.y;
    int col = blockIdx.x * TILE_DIM + threadIdx.x;
    float acc = 0.0f;

    for (int t = 0; t < (K + TILE_DIM - 1) / TILE_DIM; ++t) {
        int aCol = t * TILE_DIM + threadIdx.x;
        int bRow = t * TILE_DIM + threadIdx.y;

        sA[threadIdx.y][threadIdx.x] = (row < M && aCol < K) ? A[row * K + aCol] : 0.0f;
        sB[threadIdx.y][threadIdx.x] = (bRow < K && col < N) ? B[bRow * N + col] : 0.0f;

        __syncthreads();

        #pragma unroll
        for (int i = 0; i < TILE_DIM; ++i) {
            acc += sA[threadIdx.y][i] * sB[i][threadIdx.x];
        }

        __syncthreads();
    }

    if (row < M && col < N) {
        C[row * N + col] = acc;
    }
}

/**
 * @brief Device transpose kernel: out[j*rows+i] = in[i*cols+j]
 */
__global__ void transpose_kernel(float* __restrict__ out,
                                 const float* __restrict__ in,
                                 int rows, int cols) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < rows * cols) {
        int r = idx / cols;
        int c = idx % cols;
        out[c * rows + r] = in[r * cols + c];
    }
}

/**
 * @brief Launch transpose on device
 */
static void launch_transpose(float* out, const float* in, int rows, int cols,
                              cudaStream_t stream) {
    int n = rows * cols;
    int threads = 256;
    int blocks = (n + threads - 1) / threads;
    transpose_kernel<<<blocks, threads, 0, stream>>>(out, in, rows, cols);
}

void native_matmul(float* C, const float* A, const float* B,
                   int M, int N, int K, cudaStream_t stream) {
    dim3 block(TILE_DIM, TILE_DIM);
    dim3 grid((N + TILE_DIM - 1) / TILE_DIM, (M + TILE_DIM - 1) / TILE_DIM);
    native_tiled_matmul_kernel<<<grid, block, 0, stream>>>(C, A, B, M, N, K);
}
