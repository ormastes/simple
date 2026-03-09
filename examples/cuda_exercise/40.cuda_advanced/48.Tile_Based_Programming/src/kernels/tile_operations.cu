// tile_operations.cu - Tile-based programming using shared memory tiling

#include <cuda_runtime.h>
#include <cooperative_groups.h>

namespace cg = cooperative_groups;

// Tile size constants
constexpr int TILE_SIZE = 16;
constexpr int TILE_SIZE_32 = 32;

// Tiled matrix transpose
template<int TILE_DIM>
__global__ void tiled_transpose(float* output, const float* input, int rows, int cols) {
    __shared__ float tile[TILE_DIM][TILE_DIM + 1];  // +1 to avoid bank conflicts

    int x = blockIdx.x * TILE_DIM + threadIdx.x;
    int y = blockIdx.y * TILE_DIM + threadIdx.y;

    // Load tile from input
    if (x < cols && y < rows) {
        tile[threadIdx.y][threadIdx.x] = input[y * cols + x];
    }
    __syncthreads();

    // Compute transposed coordinates
    x = blockIdx.y * TILE_DIM + threadIdx.x;
    y = blockIdx.x * TILE_DIM + threadIdx.y;

    // Store transposed tile to output
    if (x < rows && y < cols) {
        output[y * rows + x] = tile[threadIdx.x][threadIdx.y];
    }
}

// Tiled matrix multiplication
template<int TILE_DIM>
__global__ void tiled_matmul(float* C, const float* A, const float* B, int M, int N, int K) {
    __shared__ float As[TILE_DIM][TILE_DIM];
    __shared__ float Bs[TILE_DIM][TILE_DIM];

    int row = blockIdx.y * TILE_DIM + threadIdx.y;
    int col = blockIdx.x * TILE_DIM + threadIdx.x;

    float sum = 0.0f;

    // Loop over tiles
    for (int t = 0; t < (K + TILE_DIM - 1) / TILE_DIM; t++) {
        // Load tile of A
        if (row < M && t * TILE_DIM + threadIdx.x < K) {
            As[threadIdx.y][threadIdx.x] = A[row * K + t * TILE_DIM + threadIdx.x];
        } else {
            As[threadIdx.y][threadIdx.x] = 0.0f;
        }

        // Load tile of B
        if (t * TILE_DIM + threadIdx.y < K && col < N) {
            Bs[threadIdx.y][threadIdx.x] = B[(t * TILE_DIM + threadIdx.y) * N + col];
        } else {
            Bs[threadIdx.y][threadIdx.x] = 0.0f;
        }

        __syncthreads();

        // Compute partial dot product
        for (int k = 0; k < TILE_DIM; k++) {
            sum += As[threadIdx.y][k] * Bs[k][threadIdx.x];
        }

        __syncthreads();
    }

    // Write result
    if (row < M && col < N) {
        C[row * N + col] = sum;
    }
}

// Tiled reduction using cooperative groups
__global__ void tiled_reduction(float* output, const float* input, int n) {
    __shared__ float tile[256];

    int tid = threadIdx.x;
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Load data into shared memory tile
    tile[tid] = (idx < n) ? input[idx] : 0.0f;
    __syncthreads();

    // Reduction within tile
    for (int stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (tid < stride) {
            tile[tid] += tile[tid + stride];
        }
        __syncthreads();
    }

    // Write result
    if (tid == 0) {
        output[blockIdx.x] = tile[0];
    }
}

// Tiled convolution (1D)
template<int TILE_SIZE, int FILTER_SIZE>
__global__ void tiled_conv1d(float* output, const float* input, const float* filter, int n) {
    __shared__ float tile[TILE_SIZE + FILTER_SIZE - 1];

    int tid = threadIdx.x;
    int idx = blockIdx.x * TILE_SIZE + threadIdx.x;

    // Load tile with halos
    if (idx < n + FILTER_SIZE - 1) {
        int input_idx = idx - (FILTER_SIZE / 2);
        tile[tid] = (input_idx >= 0 && input_idx < n) ? input[input_idx] : 0.0f;
    }
    __syncthreads();

    // Compute convolution
    if (tid < TILE_SIZE && idx < n) {
        float sum = 0.0f;
        for (int k = 0; k < FILTER_SIZE; k++) {
            sum += tile[tid + k] * filter[k];
        }
        output[idx] = sum;
    }
}

// Cooperative groups tiled operation
__global__ void cooperative_tiled_add(float* output, const float* A, const float* B, int n) {
    // Get the thread block group
    auto block = cg::this_thread_block();

    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n) {
        output[idx] = A[idx] + B[idx];
    }

    // Synchronize the entire block
    block.sync();
}

// Explicit template instantiations
template __global__ void tiled_transpose<16>(float*, const float*, int, int);
template __global__ void tiled_transpose<32>(float*, const float*, int, int);

template __global__ void tiled_matmul<16>(float*, const float*, const float*, int, int, int);
template __global__ void tiled_matmul<32>(float*, const float*, const float*, int, int, int);

template __global__ void tiled_conv1d<256, 5>(float*, const float*, const float*, int);
template __global__ void tiled_conv1d<256, 7>(float*, const float*, const float*, int);
