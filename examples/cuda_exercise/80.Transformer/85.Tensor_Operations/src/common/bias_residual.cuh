/**
 * @file bias_residual.cuh
 * @brief Fused bias + residual addition kernel declarations
 *
 * Combines bias addition and residual connection into a single kernel to
 * reduce global memory traffic. This pattern appears after every linear
 * projection and attention output in transformer blocks.
 */
#pragma once
#include <cuda_runtime.h>

namespace transformer {

/**
 * @brief Launch fused bias + residual addition
 *
 * Computes: output[row][col] = input[row][col] + bias[col] + residual[row][col]
 *
 * @param[out] output Result matrix [rows, cols]
 * @param[in] input Input matrix [rows, cols]
 * @param[in] bias Bias vector [cols] (broadcast along rows)
 * @param[in] residual Residual matrix [rows, cols]
 * @param[in] rows Number of rows
 * @param[in] cols Number of columns
 * @param[in] stream CUDA stream
 */
void launch_bias_residual(float* output, const float* input,
                          const float* bias, const float* residual,
                          int rows, int cols, cudaStream_t stream = 0);

} // namespace transformer
