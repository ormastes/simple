/**
 * @file torch_attention_api.cpp
 * @brief C API implementation for scaled dot-product attention
 *
 * Computes Attention(Q,K,V) = softmax(Q * K^T / sqrt(d_k)) * V with an
 * optional causal mask. The implementation allocates temporary device buffers
 * for the score matrix and the softmax output, then chains kernel launches
 * via the host-callable wrappers declared in matmul_kernel.h.
 */

#include "torch_api.h"
#include "matmul_kernel.h"
#include <cuda_runtime.h>
#include <cstdio>
#include <cmath>

extern "C" TorchStatus torch_scaled_dot_product_attention(
        TorchTensorDesc* output,
        const TorchTensorDesc* Q,
        const TorchTensorDesc* K,
        const TorchTensorDesc* V,
        int causal) {
    // ---- Validate inputs ----
    if (!output || !Q || !K || !V) {
        fprintf(stderr, "torch_sdpa: NULL descriptor\n");
        return TORCH_ERROR_INVALID_ARGUMENT;
    }
    if (!output->data || !Q->data || !K->data || !V->data) {
        fprintf(stderr, "torch_sdpa: NULL data pointer\n");
        return TORCH_ERROR_INVALID_ARGUMENT;
    }

    // Expect 3-D tensors [batch x seq_len x head_dim] for simplicity.
    // For a single-head, single-batch call, accept 2-D [seq_len x head_dim].
    int seq_len, head_dim;
    if (Q->ndim == 2) {
        seq_len = static_cast<int>(Q->shape[0]);
        head_dim = static_cast<int>(Q->shape[1]);
    } else if (Q->ndim == 3) {
        // Treat as single-batch for now; batch loop is omitted for clarity
        seq_len = static_cast<int>(Q->shape[1]);
        head_dim = static_cast<int>(Q->shape[2]);
    } else {
        fprintf(stderr, "torch_sdpa: Q must be 2-D or 3-D (got %d)\n", Q->ndim);
        return TORCH_ERROR_INVALID_ARGUMENT;
    }

    float scale = 1.0f / sqrtf(static_cast<float>(head_dim));

    // Allocate temporary: scores[seq_len x seq_len] and attn_weights[seq_len x seq_len]
    float *scores = nullptr, *attn_weights = nullptr;
    cudaError_t err;

    err = cudaMalloc(&scores, sizeof(float) * seq_len * seq_len);
    if (err != cudaSuccess) return TORCH_ERROR_OUT_OF_MEMORY;

    err = cudaMalloc(&attn_weights, sizeof(float) * seq_len * seq_len);
    if (err != cudaSuccess) {
        cudaFree(scores);
        return TORCH_ERROR_OUT_OF_MEMORY;
    }

    // Step 1: scores = Q * K^T   [seq_len x seq_len]
    // K is [seq_len x head_dim], K^T is [head_dim x seq_len]
    // Need to transpose K. Allocate K^T.
    float* K_t = nullptr;
    err = cudaMalloc(&K_t, sizeof(float) * seq_len * head_dim);
    if (err != cudaSuccess) {
        cudaFree(scores);
        cudaFree(attn_weights);
        return TORCH_ERROR_OUT_OF_MEMORY;
    }

    {
        // Transpose K on host (simple, not perf-critical for moderate sizes)
        float* k_host = new float[seq_len * head_dim];
        const float* k_src = K->data;
        err = cudaMemcpy(k_host, k_src, sizeof(float) * seq_len * head_dim,
                         cudaMemcpyDeviceToHost);
        if (err != cudaSuccess) {
            delete[] k_host;
            cudaFree(K_t);
            cudaFree(scores);
            cudaFree(attn_weights);
            return TORCH_ERROR_CUDA;
        }

        float* kt_host = new float[seq_len * head_dim];
        for (int i = 0; i < seq_len; ++i) {
            for (int j = 0; j < head_dim; ++j) {
                kt_host[j * seq_len + i] = k_host[i * head_dim + j];
            }
        }

        err = cudaMemcpy(K_t, kt_host, sizeof(float) * seq_len * head_dim,
                         cudaMemcpyHostToDevice);
        delete[] k_host;
        delete[] kt_host;
        if (err != cudaSuccess) {
            cudaFree(K_t);
            cudaFree(scores);
            cudaFree(attn_weights);
            return TORCH_ERROR_CUDA;
        }
    }

    // scores[seq x seq] = Q[seq x dim] * K_t[dim x seq]
    const float* q_src = Q->data;
    launch_tiled_matmul(scores, q_src, K_t, seq_len, seq_len, head_dim, nullptr);
    cudaFree(K_t);

    err = cudaGetLastError();
    if (err != cudaSuccess) {
        cudaFree(scores);
        cudaFree(attn_weights);
        return TORCH_ERROR_CUDA;
    }

    // Step 2: scores *= 1/sqrt(d_k)
    launch_scale(scores, scale, seq_len * seq_len, nullptr);

    // Step 3: Apply causal mask if requested
    if (causal) {
        launch_causal_mask(scores, seq_len, nullptr);
    }

    // Step 4: attn_weights = softmax(scores) along last dimension
    launch_softmax(attn_weights, scores, seq_len, seq_len, nullptr);

    // Step 5: output[seq x dim] = attn_weights[seq x seq] * V[seq x dim]
    const float* v_src = V->data;
    float* out_dst = output->data;
    launch_tiled_matmul(out_dst, attn_weights, v_src, seq_len, head_dim, seq_len, nullptr);

    err = cudaGetLastError();
    if (err != cudaSuccess) {
        cudaFree(scores);
        cudaFree(attn_weights);
        return TORCH_ERROR_CUDA;
    }

    err = cudaDeviceSynchronize();
    cudaFree(scores);
    cudaFree(attn_weights);

    if (err != cudaSuccess) return TORCH_ERROR_CUDA;

    return TORCH_SUCCESS;
}
