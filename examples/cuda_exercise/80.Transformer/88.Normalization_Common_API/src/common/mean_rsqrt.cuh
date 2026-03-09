/**
 * @file mean_rsqrt.cuh
 * @brief Mean and reciprocal square root helpers for normalization
 */
#pragma once
#include <cuda_runtime.h>
#include "reduce_block.cuh"

namespace transformer {

/**
 * @brief Compute mean of a row using block-level reduction
 * Each thread accumulates a strided portion and then the block reduces to produce the mean.
 *
 * @param[in] input Row data pointer
 * @param[in] n Number of elements
 * @param[in,out] smem Shared memory for reduction
 * @return Mean value (broadcast to all threads)
 */
__device__ __forceinline__ float compute_mean(const float* input, int n, float* smem) {
    float sum = 0.0f;
    for (int i = threadIdx.x; i < n; i += blockDim.x) {
        sum += input[i];
    }
    sum = block_reduce_sum(sum, smem);
    return sum / static_cast<float>(n);
}

/**
 * @brief Compute variance (mean of squared differences) using block reduction
 * Computes Var(x) = mean((x - mean)^2).
 *
 * @param[in] input Row data pointer
 * @param[in] mean Pre-computed mean of the row
 * @param[in] n Number of elements
 * @param[in,out] smem Shared memory for reduction
 * @return Variance value (broadcast to all threads)
 */
__device__ __forceinline__ float compute_variance(const float* input, float mean, int n, float* smem) {
    float sum_sq = 0.0f;
    for (int i = threadIdx.x; i < n; i += blockDim.x) {
        float diff = input[i] - mean;
        sum_sq += diff * diff;
    }
    sum_sq = block_reduce_sum(sum_sq, smem);
    return sum_sq / static_cast<float>(n);
}

/**
 * @brief Compute RMS (root mean square) reciprocal for RMSNorm
 * Computes rsqrt(mean(x^2) + eps), the scaling factor used in RMSNorm.
 *
 * @param[in] input Row data pointer
 * @param[in] n Number of elements
 * @param[in] eps Epsilon for numerical stability
 * @param[in,out] smem Shared memory for reduction
 * @return rsqrt(mean(x^2) + eps) (broadcast to all threads)
 */
__device__ __forceinline__ float compute_rms_rsqrt(const float* input, int n, float eps, float* smem) {
    float sum_sq = 0.0f;
    for (int i = threadIdx.x; i < n; i += blockDim.x) {
        sum_sq += input[i] * input[i];
    }
    sum_sq = block_reduce_sum(sum_sq, smem);
    float rms = sum_sq / static_cast<float>(n);
    return rsqrtf(rms + eps);
}

} // namespace transformer
