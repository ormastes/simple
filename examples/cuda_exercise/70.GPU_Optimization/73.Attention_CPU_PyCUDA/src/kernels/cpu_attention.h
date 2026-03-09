/**
 * @file cpu_attention.h
 * @brief CPU attention mechanism header for transformer models
 *
 * Provides CPU-based implementations of scaled dot-product attention,
 * causal (masked) attention, multi-head attention, and softmax used
 * as performance baselines for GPU comparison.
 */

#pragma once

#include <chrono>
#include <cstring>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Naive scaled dot-product attention: softmax(Q*K^T / sqrt(d_k)) * V
 *
 * Computes full attention over all sequence positions without masking.
 *
 * @param[out] output   Output matrix [seq_len x d_model]
 * @param[in]  Q        Query matrix [seq_len x d_model]
 * @param[in]  K        Key matrix [seq_len x d_model]
 * @param[in]  V        Value matrix [seq_len x d_model]
 * @param[in]  seq_len  Sequence length (number of tokens)
 * @param[in]  d_model  Model/embedding dimension
 */
void cpu_sdpa_naive(float* output, const float* Q, const float* K, const float* V,
                   int seq_len, int d_model);

/**
 * @brief Scaled dot-product attention with causal (lower-triangular) mask
 *
 * Masks upper triangle to -inf before softmax so that each position
 * can only attend to current and previous positions (autoregressive).
 *
 * @param[out] output   Output matrix [seq_len x d_model]
 * @param[in]  Q        Query matrix [seq_len x d_model]
 * @param[in]  K        Key matrix [seq_len x d_model]
 * @param[in]  V        Value matrix [seq_len x d_model]
 * @param[in]  seq_len  Sequence length (number of tokens)
 * @param[in]  d_model  Model/embedding dimension
 */
void cpu_sdpa_causal(float* output, const float* Q, const float* K, const float* V,
                    int seq_len, int d_model);

/**
 * @brief Multi-head attention with output projection
 *
 * Splits Q, K, V into num_heads heads, runs SDPA per head,
 * concatenates results, and projects with W_O.
 *
 * @param[out] output      Output matrix [batch_size x seq_len x d_model]
 * @param[in]  Q           Query matrix [batch_size x seq_len x d_model]
 * @param[in]  K           Key matrix [batch_size x seq_len x d_model]
 * @param[in]  V           Value matrix [batch_size x seq_len x d_model]
 * @param[in]  W_O         Output projection weight [d_model x d_model]
 * @param[in]  batch_size  Batch size
 * @param[in]  seq_len     Sequence length
 * @param[in]  d_model     Model dimension (must be divisible by num_heads)
 * @param[in]  num_heads   Number of attention heads
 */
void cpu_multi_head_attention(float* output, const float* Q, const float* K, const float* V,
                             const float* W_O, int batch_size, int seq_len, int d_model, int num_heads);

/**
 * @brief Parallel scaled dot-product attention using OpenMP
 *
 * Parallelizes across sequence positions for improved throughput.
 *
 * @param[out] output       Output matrix [seq_len x d_model]
 * @param[in]  Q            Query matrix [seq_len x d_model]
 * @param[in]  K            Key matrix [seq_len x d_model]
 * @param[in]  V            Value matrix [seq_len x d_model]
 * @param[in]  seq_len      Sequence length
 * @param[in]  d_model      Model dimension
 * @param[in]  num_threads  Number of OpenMP threads (-1 for auto)
 */
void cpu_sdpa_parallel(float* output, const float* Q, const float* K, const float* V,
                      int seq_len, int d_model, int num_threads);

/**
 * @brief Numerically stable softmax over rows
 *
 * Computes softmax(input) row-wise: subtract max, exp, normalize.
 *
 * @param[out] output  Output matrix [rows x cols], each row sums to 1.0
 * @param[in]  input   Input matrix [rows x cols]
 * @param[in]  rows    Number of rows
 * @param[in]  cols    Number of columns
 */
void cpu_softmax(float* output, const float* input, int rows, int cols);

/**
 * @brief Timed attention computation returning elapsed milliseconds
 *
 * @param[out] output   Output matrix [seq_len x d_model]
 * @param[in]  Q        Query matrix [seq_len x d_model]
 * @param[in]  K        Key matrix [seq_len x d_model]
 * @param[in]  V        Value matrix [seq_len x d_model]
 * @param[in]  seq_len  Sequence length
 * @param[in]  d_model  Model dimension
 * @param[in]  method   Method name: "naive", "causal", "parallel"
 * @return Elapsed time in milliseconds
 */
float cpu_attention_timed(float* output, const float* Q, const float* K, const float* V,
                         int seq_len, int d_model, const char* method);

#ifdef __cplusplus
}
#endif
