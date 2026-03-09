/**
 * @file 01_naive.cu
 * @brief Naive backpropagation with separate kernels for grad_input, grad_weight, grad_bias.
 *
 * Implements a simple fully-connected layer backward pass using three separate kernel
 * launches. Each kernel handles one gradient computation independently, resulting in
 * high kernel launch overhead and redundant global memory reads.
 */

#include "backprop/01_naive.h"
#include <cuda_runtime.h>

namespace opt78 {

/**
 * @brief Compute gradient w.r.t. input: grad_input = grad_output * W^T
 *
 * @param[out] grad_input  [batch x in_features]
 * @param[in]  grad_output [batch x out_features]
 * @param[in]  weight      [out_features x in_features]
 * @param[in]  batch       Batch size
 * @param[in]  in_features Input feature dimension
 * @param[in]  out_features Output feature dimension
 */
__global__ void grad_input_kernel(float* __restrict__ grad_input,
                                   const float* __restrict__ grad_output,
                                   const float* __restrict__ weight,
                                   int batch, int in_features, int out_features) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < batch && col < in_features) {
        float sum = 0.0f;
        for (int k = 0; k < out_features; ++k) {
            sum += grad_output[row * out_features + k] * weight[k * in_features + col];
        }
        grad_input[row * in_features + col] = sum;
    }
}

/**
 * @brief Compute gradient w.r.t. weight: grad_weight = grad_output^T * input
 *
 * @param[out] grad_weight [out_features x in_features]
 * @param[in]  grad_output [batch x out_features]
 * @param[in]  input       [batch x in_features]
 * @param[in]  batch       Batch size
 * @param[in]  in_features Input feature dimension
 * @param[in]  out_features Output feature dimension
 */
__global__ void grad_weight_kernel(float* __restrict__ grad_weight,
                                    const float* __restrict__ grad_output,
                                    const float* __restrict__ input,
                                    int batch, int in_features, int out_features) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < out_features && col < in_features) {
        float sum = 0.0f;
        for (int b = 0; b < batch; ++b) {
            sum += grad_output[b * out_features + row] * input[b * in_features + col];
        }
        grad_weight[row * in_features + col] = sum;
    }
}

/**
 * @brief Compute gradient w.r.t. bias: grad_bias = sum(grad_output, dim=0)
 *
 * @param[out] grad_bias   [out_features]
 * @param[in]  grad_output [batch x out_features]
 * @param[in]  batch       Batch size
 * @param[in]  out_features Output feature dimension
 */
__global__ void grad_bias_kernel(float* __restrict__ grad_bias,
                                  const float* __restrict__ grad_output,
                                  int batch, int out_features) {
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (col < out_features) {
        float sum = 0.0f;
        for (int b = 0; b < batch; ++b) {
            sum += grad_output[b * out_features + col];
        }
        grad_bias[col] = sum;
    }
}

void backprop_naive(float* grad_input, float* grad_weight, float* grad_bias,
                    const float* grad_output, const float* input,
                    const float* weight,
                    int batch, int in_features, int out_features,
                    cudaStream_t s) {
    dim3 block(16, 16);

    // grad_input = grad_output * W^T
    {
        dim3 grid((in_features + block.x - 1) / block.x,
                  (batch + block.y - 1) / block.y);
        grad_input_kernel<<<grid, block, 0, s>>>(
            grad_input, grad_output, weight, batch, in_features, out_features);
    }

    // grad_weight = grad_output^T * input
    {
        dim3 grid((in_features + block.x - 1) / block.x,
                  (out_features + block.y - 1) / block.y);
        grad_weight_kernel<<<grid, block, 0, s>>>(
            grad_weight, grad_output, input, batch, in_features, out_features);
    }

    // grad_bias = sum(grad_output, dim=0)
    {
        int threads = 256;
        int blocks = (out_features + threads - 1) / threads;
        grad_bias_kernel<<<blocks, threads, 0, s>>>(
            grad_bias, grad_output, batch, out_features);
    }
}

}  // namespace opt78
