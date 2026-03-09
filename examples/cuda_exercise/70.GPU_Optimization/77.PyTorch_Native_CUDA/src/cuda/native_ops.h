/**
 * @file native_ops.h
 * @brief Host-callable CUDA kernel launchers for PyTorch native extension
 *
 * Declares the C++ functions that the pybind11 bindings layer calls.
 * Each function accepts raw device pointers and dimensions, launches the
 * appropriate CUDA kernel, and synchronises before returning.
 */
#pragma once
#include <cuda_runtime.h>

/**
 * @brief Tiled matrix multiplication C = A * B
 *
 * @param[out] C       Output [M x N], device memory
 * @param[in]  A       Input  [M x K], device memory
 * @param[in]  B       Input  [K x N], device memory
 * @param[in]  M       Rows of A/C
 * @param[in]  N       Columns of B/C
 * @param[in]  K       Inner dimension
 * @param[in]  stream  CUDA stream
 */
void native_matmul(float* C, const float* A, const float* B,
                   int M, int N, int K, cudaStream_t stream = nullptr);

/**
 * @brief Fused linear backward pass
 *
 * Computes grad_input, grad_weight, and grad_bias in one call.
 *
 * @param[out] grad_input   [batch x in_features]
 * @param[out] grad_weight  [out_features x in_features]
 * @param[out] grad_bias    [out_features] (may be nullptr to skip)
 * @param[in]  grad_output  [batch x out_features]
 * @param[in]  input        [batch x in_features]
 * @param[in]  weight       [out_features x in_features]
 * @param[in]  batch        Batch size
 * @param[in]  in_features  Input feature count
 * @param[in]  out_features Output feature count
 * @param[in]  stream       CUDA stream
 */
void native_linear_backward(float* grad_input, float* grad_weight, float* grad_bias,
                             const float* grad_output, const float* input,
                             const float* weight,
                             int batch, int in_features, int out_features,
                             cudaStream_t stream = nullptr);

/**
 * @brief Linear forward: output = input * weight^T + bias
 *
 * @param[out] output   [batch x out_features]
 * @param[in]  input    [batch x in_features]
 * @param[in]  weight   [out_features x in_features]
 * @param[in]  bias     [out_features] (may be nullptr)
 * @param[in]  batch    Batch size
 * @param[in]  in_f     Input features
 * @param[in]  out_f    Output features
 * @param[in]  stream   CUDA stream
 */
void native_linear_forward(float* output, const float* input, const float* weight,
                            const float* bias, int batch, int in_f, int out_f,
                            cudaStream_t stream = nullptr);

/**
 * @brief Scaled dot-product attention
 *
 * Computes Attention(Q,K,V) = softmax(Q*K^T / sqrt(d_k)) * V.
 *
 * @param[out] output   [seq_len x head_dim]
 * @param[in]  Q        [seq_len x head_dim]
 * @param[in]  K        [seq_len x head_dim]
 * @param[in]  V        [seq_len x head_dim]
 * @param[in]  seq_len  Sequence length
 * @param[in]  head_dim Head dimension
 * @param[in]  causal   Whether to apply causal mask
 * @param[in]  stream   CUDA stream
 */
void native_attention(float* output, const float* Q, const float* K, const float* V,
                      int seq_len, int head_dim, bool causal,
                      cudaStream_t stream = nullptr);
