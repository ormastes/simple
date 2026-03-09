/**
 * @file matmul_kernel.h
 * @brief Host-callable launch wrappers for CUDA kernels
 *
 * Declares the host-side functions that configure grid/block dimensions and
 * launch the underlying CUDA kernels. These wrappers are consumed by the C API
 * layer so that kernel launch details stay encapsulated in the .cu translation unit.
 */
#pragma once
#include <cuda_runtime.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Launch tiled matrix multiplication: C[MxN] = A[MxK] * B[KxN]
 *
 * @param[out] C       Output matrix, device memory
 * @param[in]  A       Left input matrix, device memory
 * @param[in]  B       Right input matrix, device memory
 * @param[in]  M       Rows of A/C
 * @param[in]  N       Columns of B/C
 * @param[in]  K       Columns of A / rows of B
 * @param[in]  stream  CUDA stream (0 for default)
 */
void launch_tiled_matmul(float* C, const float* A, const float* B,
                         int M, int N, int K, cudaStream_t stream);

/**
 * @brief Add bias vector to every row: output[i][j] += bias[j]
 *
 * @param[in,out] output  Matrix [rows x cols], device memory
 * @param[in]     bias    Bias vector [cols], device memory
 * @param[in]     rows    Number of rows
 * @param[in]     cols    Number of columns
 * @param[in]     stream  CUDA stream
 */
void launch_add_bias(float* output, const float* bias, int rows, int cols,
                     cudaStream_t stream);

/**
 * @brief Row-wise softmax
 *
 * @param[out] output  Result [rows x cols], device memory
 * @param[in]  input   Input  [rows x cols], device memory
 * @param[in]  rows    Number of rows
 * @param[in]  cols    Number of columns
 * @param[in]  stream  CUDA stream
 */
void launch_softmax(float* output, const float* input, int rows, int cols,
                    cudaStream_t stream);

/**
 * @brief Apply causal mask (set upper triangle to -inf)
 *
 * @param[in,out] scores   Score matrix [seq_len x seq_len], device memory
 * @param[in]     seq_len  Sequence length
 * @param[in]     stream   CUDA stream
 */
void launch_causal_mask(float* scores, int seq_len, cudaStream_t stream);

/**
 * @brief Reduce rows to column sums: output[j] = sum_i input[i][j]
 *
 * @param[out] output  Column sums [cols], device memory
 * @param[in]  input   Input matrix [rows x cols], device memory
 * @param[in]  rows    Number of rows
 * @param[in]  cols    Number of columns
 * @param[in]  stream  CUDA stream
 */
void launch_reduce_rows(float* output, const float* input, int rows, int cols,
                        cudaStream_t stream);

/**
 * @brief Element-wise scale: data[i] *= scale
 *
 * @param[in,out] data    Array to scale, device memory
 * @param[in]     scale   Scale factor
 * @param[in]     n       Number of elements
 * @param[in]     stream  CUDA stream
 */
void launch_scale(float* data, float scale, int n, cudaStream_t stream);

#ifdef __cplusplus
}
#endif
