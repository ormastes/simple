/**
 * @file transpose_permute.cuh
 * @brief General tensor transpose declarations
 *
 * Provides a shared-memory-optimized 2D matrix transpose for use in
 * attention head reshaping and layout conversions. Uses the +1 padding
 * technique to avoid shared memory bank conflicts.
 */
#pragma once
#include <cuda_runtime.h>

namespace transformer {

/**
 * @brief Launch 2D matrix transpose: output = input^T
 *
 * Uses shared memory tiles with +1 column padding to avoid bank conflicts.
 * Input is [rows, cols], output is [cols, rows].
 *
 * @param[out] output Transposed matrix [cols, rows]
 * @param[in] input Input matrix [rows, cols]
 * @param[in] rows Number of rows in input
 * @param[in] cols Number of columns in input
 * @param[in] stream CUDA stream
 */
void launch_transpose(float* output, const float* input, int rows, int cols,
                      cudaStream_t stream = 0);

} // namespace transformer
