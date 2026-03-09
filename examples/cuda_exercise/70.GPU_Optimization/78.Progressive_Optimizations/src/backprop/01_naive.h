/**
 * @file 01_naive.h
 * @brief Naive backpropagation - separate kernels for each gradient.
 */

#pragma once
#include <cuda_runtime.h>

namespace opt78 {

/**
 * @brief Naive backpropagation for a fully-connected layer.
 *
 * Computes grad_input, grad_weight, and grad_bias using three separate kernel
 * launches. This is the baseline for comparison with fused approaches.
 *
 * @param[out] grad_input   [batch x in_features] (device)
 * @param[out] grad_weight  [out_features x in_features] (device)
 * @param[out] grad_bias    [out_features] (device)
 * @param[in]  grad_output  [batch x out_features] (device)
 * @param[in]  input        [batch x in_features] (device)
 * @param[in]  weight       [out_features x in_features] (device)
 * @param[in]  batch        Batch size
 * @param[in]  in_features  Input feature count
 * @param[in]  out_features Output feature count
 * @param[in]  s            CUDA stream (default 0)
 */
void backprop_naive(float* grad_input, float* grad_weight, float* grad_bias,
                    const float* grad_output, const float* input,
                    const float* weight,
                    int batch, int in_features, int out_features,
                    cudaStream_t s = 0);

}  // namespace opt78
