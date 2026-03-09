/**
 * @file 02_fused.h
 * @brief Fused forward+backward reducing kernel launch overhead.
 */

#pragma once
#include <cuda_runtime.h>

namespace opt78 {

/**
 * @brief Fused forward pass: output = ReLU(input * W^T + bias).
 *
 * Computes forward pass and stores ReLU mask for backward reuse.
 *
 * @param[out] output       [batch x out_features] (device)
 * @param[out] relu_mask    [batch x out_features] (device)
 * @param[in]  input        [batch x in_features] (device)
 * @param[in]  weight       [out_features x in_features] (device)
 * @param[in]  bias         [out_features] (device)
 * @param[in]  batch        Batch size
 * @param[in]  in_features  Input feature count
 * @param[in]  out_features Output feature count
 * @param[in]  s            CUDA stream (default 0)
 */
void forward_fused(float* output, float* relu_mask,
                   const float* input, const float* weight, const float* bias,
                   int batch, int in_features, int out_features,
                   cudaStream_t s = 0);

/**
 * @brief Fused backward pass with fewer kernel launches.
 *
 * Computes grad_weight and grad_bias in a single kernel, plus grad_input separately.
 * Requires ReLU mask from the forward pass.
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
void backprop_fused(float* grad_input, float* grad_weight, float* grad_bias,
                    const float* grad_output, const float* input,
                    const float* weight, const float* relu_mask,
                    int batch, int in_features, int out_features,
                    cudaStream_t s = 0);

}  // namespace opt78
