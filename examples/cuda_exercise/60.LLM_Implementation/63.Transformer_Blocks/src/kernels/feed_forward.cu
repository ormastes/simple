/**
 * @file feed_forward.cu
 * @brief CUDA kernel implementation for Feed-Forward Network
 *
 * Implements the position-wise FFN with naive matrix multiplication and
 * GELU activation. The FFN consists of:
 *   hidden = GELU(input * W1 + b1)
 *   output = hidden * W2 + b2
 */

#include "common/feed_forward.h"
#include "cuda_utils.h"
#include <vector>
#include <random>
#include <cmath>

namespace llm {

/**
 * @brief Naive matrix multiplication kernel with optional bias
 *
 * Each thread computes one element of the output matrix.
 * C[i][j] = sum_k(A[i][k] * B[k][j]) + bias[j]
 */
__global__ void matmul_bias_kernel(float* C, const float* A, const float* B,
                                   const float* bias, int M, int K, int N) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < M && col < N) {
        float sum = 0.0f;
        for (int k = 0; k < K; ++k) {
            sum += A[row * K + k] * B[k * N + col];
        }
        if (bias != nullptr) {
            sum += bias[col];
        }
        C[row * N + col] = sum;
    }
}

/**
 * @brief GELU activation kernel (in-place)
 *
 * Uses the approximation:
 * GELU(x) = 0.5 * x * (1 + tanh(sqrt(2/pi) * (x + 0.044715 * x^3)))
 */
__global__ void gelu_kernel(float* data, int size) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < size) {
        float x = data[idx];
        // Approximate GELU using tanh
        const float sqrt_2_over_pi = 0.7978845608f;  // sqrt(2/pi)
        float cdf = 0.5f * (1.0f + tanhf(sqrt_2_over_pi * (x + 0.044715f * x * x * x)));
        data[idx] = x * cdf;
    }
}

void ffn_forward(float* output, const float* input, const FFNWeights& weights,
                const FFNConfig& config, int batch_size, int seq_len,
                cudaStream_t stream) {
    int M = batch_size * seq_len;  // total number of tokens
    int K = config.d_model;
    int N = config.d_ff;

    // Allocate intermediate buffer for hidden layer
    float* hidden = cuda_malloc<float>(M * N);

    // Step 1: hidden = input * W1 + b1
    {
        dim3 block(16, 16);
        dim3 grid((N + block.x - 1) / block.x,
                  (M + block.y - 1) / block.y);
        matmul_bias_kernel<<<grid, block, 0, stream>>>(
            hidden, input, weights.W1, weights.b1, M, K, N);
        CHECK_CUDA(cudaGetLastError());
    }

    // Step 2: hidden = GELU(hidden)
    {
        int total = M * N;
        int block_size = 256;
        int grid_size = (total + block_size - 1) / block_size;
        gelu_kernel<<<grid_size, block_size, 0, stream>>>(hidden, total);
        CHECK_CUDA(cudaGetLastError());
    }

    // Step 3: output = hidden * W2 + b2
    {
        int M2 = M;
        int K2 = N;        // d_ff
        int N2 = K;        // d_model
        dim3 block(16, 16);
        dim3 grid((N2 + block.x - 1) / block.x,
                  (M2 + block.y - 1) / block.y);
        matmul_bias_kernel<<<grid, block, 0, stream>>>(
            output, hidden, weights.W2, weights.b2, M2, K2, N2);
        CHECK_CUDA(cudaGetLastError());
    }

    cuda_free(hidden);
}

FFNWeights allocate_ffn_weights(const FFNConfig& config) {
    FFNWeights weights;

    // Allocate weight matrices and bias vectors
    weights.W1 = cuda_malloc<float>(config.d_model * config.d_ff);
    weights.b1 = cuda_calloc<float>(config.d_ff);
    weights.W2 = cuda_malloc<float>(config.d_ff * config.d_model);
    weights.b2 = cuda_calloc<float>(config.d_model);

    // Xavier initialization for W1 and W2
    std::default_random_engine gen(42);

    {
        float scale = 1.0f / std::sqrt(static_cast<float>(config.d_model));
        std::normal_distribution<float> dist(0.0f, scale);
        std::vector<float> h_W1(config.d_model * config.d_ff);
        for (auto& v : h_W1) v = dist(gen);
        CHECK_CUDA(cudaMemcpy(weights.W1, h_W1.data(),
                              h_W1.size() * sizeof(float), cudaMemcpyHostToDevice));
    }

    {
        float scale = 1.0f / std::sqrt(static_cast<float>(config.d_ff));
        std::normal_distribution<float> dist(0.0f, scale);
        std::vector<float> h_W2(config.d_ff * config.d_model);
        for (auto& v : h_W2) v = dist(gen);
        CHECK_CUDA(cudaMemcpy(weights.W2, h_W2.data(),
                              h_W2.size() * sizeof(float), cudaMemcpyHostToDevice));
    }

    return weights;
}

void free_ffn_weights(FFNWeights& weights) {
    cuda_free(weights.W1);
    cuda_free(weights.b1);
    cuda_free(weights.W2);
    cuda_free(weights.b2);
    weights.W1 = nullptr;
    weights.b1 = nullptr;
    weights.W2 = nullptr;
    weights.b2 = nullptr;
}

} // namespace llm
