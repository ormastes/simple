/**
 * @file 02_fused.cu
 * @brief Fused forward+backward pass reducing kernel launch overhead.
 *
 * Combines the forward pass (output = ReLU(input * W^T + bias)) with the backward
 * pass into fewer kernel launches. The forward pass stores the ReLU mask for reuse
 * during the backward pass, and grad_weight + grad_bias are computed in a single
 * fused kernel.
 */

#include "backprop/02_fused.h"
#include <cuda_runtime.h>

namespace opt78 {

/**
 * @brief Fused forward pass: output = ReLU(input * W^T + bias), storing the ReLU mask.
 *
 * @param[out] output    [batch x out_features]
 * @param[out] relu_mask [batch x out_features] (1.0 if activated, 0.0 otherwise)
 * @param[in]  input     [batch x in_features]
 * @param[in]  weight    [out_features x in_features]
 * @param[in]  bias      [out_features]
 * @param[in]  batch     Batch size
 * @param[in]  in_features Input features
 * @param[in]  out_features Output features
 */
__global__ void fused_forward_kernel(float* __restrict__ output,
                                      float* __restrict__ relu_mask,
                                      const float* __restrict__ input,
                                      const float* __restrict__ weight,
                                      const float* __restrict__ bias,
                                      int batch, int in_features, int out_features) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < batch && col < out_features) {
        float sum = bias[col];
        for (int k = 0; k < in_features; ++k) {
            sum += input[row * in_features + k] * weight[col * in_features + k];
        }
        // ReLU activation
        bool active = (sum > 0.0f);
        output[row * out_features + col] = active ? sum : 0.0f;
        relu_mask[row * out_features + col] = active ? 1.0f : 0.0f;
    }
}

/**
 * @brief Fused backward kernel: compute grad_weight and grad_bias together.
 *
 * Reduces kernel launches from 3 to 2 by computing both weight and bias gradients
 * in a single kernel, using shared memory reduction for bias.
 *
 * @param[out] grad_weight  [out_features x in_features]
 * @param[out] grad_bias    [out_features]
 * @param[in]  grad_output  [batch x out_features]
 * @param[in]  input        [batch x in_features]
 * @param[in]  relu_mask    [batch x out_features]
 * @param[in]  batch        Batch size
 * @param[in]  in_features  Input features
 * @param[in]  out_features Output features
 */
__global__ void fused_grad_weight_bias_kernel(float* __restrict__ grad_weight,
                                               float* __restrict__ grad_bias,
                                               const float* __restrict__ grad_output,
                                               const float* __restrict__ input,
                                               const float* __restrict__ relu_mask,
                                               int batch, int in_features, int out_features) {
    int out_idx = blockIdx.y;
    int in_idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (out_idx < out_features) {
        // Compute grad_weight[out_idx][in_idx]
        if (in_idx < in_features) {
            float sum = 0.0f;
            for (int b = 0; b < batch; ++b) {
                float masked_grad = grad_output[b * out_features + out_idx] *
                                    relu_mask[b * out_features + out_idx];
                sum += masked_grad * input[b * in_features + in_idx];
            }
            grad_weight[out_idx * in_features + in_idx] = sum;
        }

        // First thread also computes grad_bias for this output feature
        if (threadIdx.x == 0 && blockIdx.x == 0) {
            float bias_sum = 0.0f;
            for (int b = 0; b < batch; ++b) {
                bias_sum += grad_output[b * out_features + out_idx] *
                            relu_mask[b * out_features + out_idx];
            }
            grad_bias[out_idx] = bias_sum;
        }
    }
}

/**
 * @brief Backward pass for grad_input with ReLU mask applied.
 *
 * @param[out] grad_input  [batch x in_features]
 * @param[in]  grad_output [batch x out_features]
 * @param[in]  weight      [out_features x in_features]
 * @param[in]  relu_mask   [batch x out_features]
 * @param[in]  batch       Batch size
 * @param[in]  in_features Input features
 * @param[in]  out_features Output features
 */
__global__ void fused_grad_input_kernel(float* __restrict__ grad_input,
                                         const float* __restrict__ grad_output,
                                         const float* __restrict__ weight,
                                         const float* __restrict__ relu_mask,
                                         int batch, int in_features, int out_features) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < batch && col < in_features) {
        float sum = 0.0f;
        for (int k = 0; k < out_features; ++k) {
            float masked_grad = grad_output[row * out_features + k] *
                                relu_mask[row * out_features + k];
            sum += masked_grad * weight[k * in_features + col];
        }
        grad_input[row * in_features + col] = sum;
    }
}

void backprop_fused(float* grad_input, float* grad_weight, float* grad_bias,
                    const float* grad_output, const float* input,
                    const float* weight, const float* relu_mask,
                    int batch, int in_features, int out_features,
                    cudaStream_t s) {
    dim3 block(16, 16);

    // Fused grad_weight + grad_bias (1 kernel instead of 2)
    {
        int threads = 256;
        dim3 grid_wb((in_features + threads - 1) / threads, out_features);
        fused_grad_weight_bias_kernel<<<grid_wb, threads, 0, s>>>(
            grad_weight, grad_bias, grad_output, input, relu_mask,
            batch, in_features, out_features);
    }

    // grad_input (still separate, needs W^T)
    {
        dim3 grid((in_features + block.x - 1) / block.x,
                  (batch + block.y - 1) / block.y);
        fused_grad_input_kernel<<<grid, block, 0, s>>>(
            grad_input, grad_output, weight, relu_mask,
            batch, in_features, out_features);
    }
}

void forward_fused(float* output, float* relu_mask,
                   const float* input, const float* weight, const float* bias,
                   int batch, int in_features, int out_features,
                   cudaStream_t s) {
    dim3 block(16, 16);
    dim3 grid((out_features + block.x - 1) / block.x,
              (batch + block.y - 1) / block.y);
    fused_forward_kernel<<<grid, block, 0, s>>>(
        output, relu_mask, input, weight, bias, batch, in_features, out_features);
}

}  // namespace opt78
