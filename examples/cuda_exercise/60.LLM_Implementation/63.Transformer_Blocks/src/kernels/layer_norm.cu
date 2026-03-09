/**
 * @file layer_norm.cu
 * @brief CUDA kernel implementation for Layer Normalization
 *
 * Implements per-row normalization using shared memory reductions for
 * computing mean and variance. Each thread block processes one row.
 */

#include "common/layer_norm.h"
#include "cuda_utils.h"
#include <vector>

namespace llm {

/**
 * @brief Layer Normalization kernel
 *
 * Algorithm:
 * 1. Each thread accumulates partial sums for elements it processes
 * 2. Shared memory reduction computes the row mean
 * 3. Second pass accumulates squared deviations from the mean
 * 4. Shared memory reduction computes the row variance
 * 5. Each thread normalizes its elements: gamma * (x - mean) / sqrt(var + eps) + beta
 */
__global__ void layer_norm_kernel(float* output, const float* input,
                                  const float* gamma, const float* beta,
                                  int hidden_dim, float eps) {
    // Each block handles one row
    int row = blockIdx.x;
    int tid = threadIdx.x;
    int block_size = blockDim.x;

    const float* row_input = input + row * hidden_dim;
    float* row_output = output + row * hidden_dim;

    // Shared memory for reductions
    extern __shared__ float shared[];
    float* s_sum = shared;              // [block_size]
    float* s_sum_sq = shared + block_size; // [block_size]

    // Step 1: Compute partial sum for mean
    float local_sum = 0.0f;
    for (int i = tid; i < hidden_dim; i += block_size) {
        local_sum += row_input[i];
    }
    s_sum[tid] = local_sum;
    __syncthreads();

    // Reduction for mean
    for (int stride = block_size / 2; stride > 0; stride >>= 1) {
        if (tid < stride) {
            s_sum[tid] += s_sum[tid + stride];
        }
        __syncthreads();
    }
    float mean = s_sum[0] / hidden_dim;
    __syncthreads();

    // Step 2: Compute partial sum of squared deviations for variance
    float local_sum_sq = 0.0f;
    for (int i = tid; i < hidden_dim; i += block_size) {
        float diff = row_input[i] - mean;
        local_sum_sq += diff * diff;
    }
    s_sum_sq[tid] = local_sum_sq;
    __syncthreads();

    // Reduction for variance
    for (int stride = block_size / 2; stride > 0; stride >>= 1) {
        if (tid < stride) {
            s_sum_sq[tid] += s_sum_sq[tid + stride];
        }
        __syncthreads();
    }
    float variance = s_sum_sq[0] / hidden_dim;
    float inv_std = rsqrtf(variance + eps);
    __syncthreads();

    // Step 3: Normalize and apply gamma/beta
    for (int i = tid; i < hidden_dim; i += block_size) {
        float normalized = (row_input[i] - mean) * inv_std;
        row_output[i] = gamma[i] * normalized + beta[i];
    }
}

void layer_norm_forward(float* output, const float* input,
                       const float* gamma, const float* beta,
                       int batch_size, int hidden_dim, float eps,
                       cudaStream_t stream) {
    int block_size = (hidden_dim < 1024) ? hidden_dim : 1024;
    // Round up to next power of 2 for efficient reduction
    int rounded = 1;
    while (rounded < block_size) rounded <<= 1;
    if (rounded > 1024) rounded = 1024;
    block_size = rounded;

    dim3 grid(batch_size);
    dim3 block(block_size);
    size_t shared_mem = 2 * block_size * sizeof(float);

    layer_norm_kernel<<<grid, block, shared_mem, stream>>>(
        output, input, gamma, beta, hidden_dim, eps);
    CHECK_CUDA(cudaGetLastError());
}

LayerNormWeights allocate_layer_norm_weights(int hidden_dim) {
    LayerNormWeights weights;
    weights.gamma = cuda_malloc<float>(hidden_dim);
    weights.beta = cuda_malloc<float>(hidden_dim);

    // Initialize gamma = 1.0, beta = 0.0
    std::vector<float> h_gamma(hidden_dim, 1.0f);
    std::vector<float> h_beta(hidden_dim, 0.0f);
    CHECK_CUDA(cudaMemcpy(weights.gamma, h_gamma.data(),
                          hidden_dim * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(weights.beta, h_beta.data(),
                          hidden_dim * sizeof(float), cudaMemcpyHostToDevice));
    return weights;
}

void free_layer_norm_weights(LayerNormWeights& weights) {
    cuda_free(weights.gamma);
    cuda_free(weights.beta);
    weights.gamma = nullptr;
    weights.beta = nullptr;
}

} // namespace llm
