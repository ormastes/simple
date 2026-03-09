/**
 * @file swiglu_fused.cu
 * @brief Fused CUDA kernel for SwiGLU feed-forward network
 *
 * Implements the SwiGLU activation function used in DeepSeek R1 and LLaMA:
 *   output = W_down * (SiLU(W_gate * x) * (W_up * x))
 *
 * The gate and up projections are computed via naive matmul kernels, then
 * the SiLU gating and element-wise multiplication are fused into a single
 * kernel to reduce global memory traffic for the intermediate activations.
 */

#include "common/swiglu_ffn.h"
#include "cuda_utils.h"
#include <cmath>

namespace llm {

/**
 * @brief Naive matmul kernel: Y = X * W^T + b
 *
 * @param[out] Y          Output [M, N]
 * @param[in]  X          Input [M, K]
 * @param[in]  W          Weight [N, K]
 * @param[in]  bias       Bias [N] (may be nullptr)
 * @param[in]  M          Number of rows (total tokens)
 * @param[in]  K          Input dimension
 * @param[in]  N          Output dimension
 */
__global__ void swiglu_matmul_kernel(
    float* Y, const float* X, const float* W, const float* bias,
    int M, int K, int N
) {
    int row = blockIdx.x * blockDim.x + threadIdx.x;
    int col = blockIdx.y * blockDim.y + threadIdx.y;

    if (row < M && col < N) {
        float sum = 0.0f;
        for (int k = 0; k < K; ++k) {
            sum += X[row * K + k] * W[col * K + k];
        }
        if (bias) sum += bias[col];
        Y[row * N + col] = sum;
    }
}

/**
 * @brief Fused SiLU gate and element-wise multiply kernel
 *
 * Computes: output[i] = SiLU(gate[i]) * up[i]
 * where SiLU(x) = x * sigmoid(x) = x / (1 + exp(-x))
 *
 * Fusing these operations avoids writing gate and up results to global
 * memory separately, reducing memory bandwidth by ~2x for this step.
 *
 * @param[out] output  Fused output [total_elements]
 * @param[in]  gate    Gate projection [total_elements]
 * @param[in]  up      Up projection [total_elements]
 * @param[in]  total   Total number of elements (batch * seq * d_ff)
 */
__global__ void swiglu_fused_activation_kernel(
    float* output, const float* gate, const float* up, int total
) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < total) {
        float g = gate[idx];
        // SiLU(x) = x * sigmoid(x)
        float sigmoid_g = 1.0f / (1.0f + expf(-g));
        float silu_g = g * sigmoid_g;
        output[idx] = silu_g * up[idx];
    }
}

void swiglu_forward(float* output, const float* input,
                    const SwiGLUWeights& weights,
                    int d_model, int d_ff,
                    int batch_size, int seq_len,
                    cudaStream_t stream) {
    int total_tokens = batch_size * seq_len;

    // Allocate intermediate buffers
    float *d_gate = nullptr, *d_up = nullptr, *d_fused = nullptr;
    CHECK_CUDA(cudaMalloc(&d_gate, total_tokens * d_ff * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_up, total_tokens * d_ff * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_fused, total_tokens * d_ff * sizeof(float)));

    dim3 block(16, 16);

    // Step 1: gate = W_gate * input + b_gate  [total_tokens, d_ff]
    dim3 grid_up((total_tokens + 15) / 16, (d_ff + 15) / 16);
    swiglu_matmul_kernel<<<grid_up, block, 0, stream>>>(
        d_gate, input, weights.W_gate, weights.b_gate,
        total_tokens, d_model, d_ff);

    // Step 2: up = W_up * input + b_up  [total_tokens, d_ff]
    swiglu_matmul_kernel<<<grid_up, block, 0, stream>>>(
        d_up, input, weights.W_up, weights.b_up,
        total_tokens, d_model, d_ff);

    // Step 3: fused = SiLU(gate) * up
    int total_elements = total_tokens * d_ff;
    int act_threads = 256;
    int act_blocks = (total_elements + act_threads - 1) / act_threads;
    swiglu_fused_activation_kernel<<<act_blocks, act_threads, 0, stream>>>(
        d_fused, d_gate, d_up, total_elements);

    // Step 4: output = W_down * fused + b_down  [total_tokens, d_model]
    dim3 grid_down((total_tokens + 15) / 16, (d_model + 15) / 16);
    swiglu_matmul_kernel<<<grid_down, block, 0, stream>>>(
        output, d_fused, weights.W_down, weights.b_down,
        total_tokens, d_ff, d_model);

    CHECK_CUDA(cudaStreamSynchronize(stream));

    cudaFree(d_gate);
    cudaFree(d_up);
    cudaFree(d_fused);
}

} // namespace llm
