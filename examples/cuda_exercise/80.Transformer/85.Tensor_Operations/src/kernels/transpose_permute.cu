/**
 * @file transpose_permute.cu
 * @brief General tensor transpose with shared memory optimization
 */
#include <cuda_runtime.h>

namespace transformer {

#define TILE_DIM 32
#define BLOCK_ROWS 8

__global__ void transpose_kernel(float* output, const float* input, int rows, int cols) {
    __shared__ float tile[TILE_DIM][TILE_DIM + 1];  // +1 to avoid bank conflicts

    int x = blockIdx.x * TILE_DIM + threadIdx.x;
    int y = blockIdx.y * TILE_DIM + threadIdx.y;

    for (int j = 0; j < TILE_DIM; j += BLOCK_ROWS) {
        if (x < cols && (y + j) < rows) {
            tile[threadIdx.y + j][threadIdx.x] = input[(y + j) * cols + x];
        }
    }
    __syncthreads();

    x = blockIdx.y * TILE_DIM + threadIdx.x;
    y = blockIdx.x * TILE_DIM + threadIdx.y;

    for (int j = 0; j < TILE_DIM; j += BLOCK_ROWS) {
        if (x < rows && (y + j) < cols) {
            output[(y + j) * rows + x] = tile[threadIdx.x][threadIdx.y + j];
        }
    }
}

void launch_transpose(float* output, const float* input, int rows, int cols,
                      cudaStream_t stream = 0) {
    dim3 block(TILE_DIM, BLOCK_ROWS);
    dim3 grid((cols + TILE_DIM - 1) / TILE_DIM, (rows + TILE_DIM - 1) / TILE_DIM);
    transpose_kernel<<<grid, block, 0, stream>>>(output, input, rows, cols);
}

#undef TILE_DIM
#undef BLOCK_ROWS

} // namespace transformer
