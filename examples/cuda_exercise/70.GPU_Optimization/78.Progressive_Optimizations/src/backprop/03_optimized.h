/**
 * @file 03_optimized.h
 * @brief Optimized backpropagation with shared memory tiling and vectorized loads.
 */

#pragma once
#include <cuda_runtime.h>

namespace opt78 {

/**
 * @brief Optimized backward pass with shared memory and vectorized loads.
 *
 * Uses tiled shared memory access for the grad_input computation and fused
 * shared memory reduction for grad_weight + grad_bias.
 *
 * @param[out] grad_input   [batch x in_features] (device)
 * @param[out] grad_weight  [out_features x in_features] (device)
 * @param[out] grad_bias    [out_features] (device)
 * @param[in]  grad_output  [batch x out_features] (device)
 * @param[in]  input        [batch x in_features] (device)
 * @param[in]  weight       [out_features x in_features] (device)
 * @param[in]  relu_mask    [batch x out_features] (device)
 * @param[in]  batch        Batch size
 * @param[in]  in_features  Input feature count
 * @param[in]  out_features Output feature count
 * @param[in]  s            CUDA stream (default 0)
 */
void backprop_optimized(float* grad_input, float* grad_weight, float* grad_bias,
                         const float* grad_output, const float* input,
                         const float* weight, const float* relu_mask,
                         int batch, int in_features, int out_features,
                         cudaStream_t s = 0);

}  // namespace opt78
