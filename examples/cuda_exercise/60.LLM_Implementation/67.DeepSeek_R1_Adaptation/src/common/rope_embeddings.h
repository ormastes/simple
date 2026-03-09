/**
 * @file rope_embeddings.h
 * @brief Rotary Position Embeddings (RoPE) interface
 *
 * Implements RoPE as described in Su et al. (2021) "RoFormer: Enhanced Transformer
 * with Rotary Position Embedding". RoPE encodes position information by rotating
 * pairs of dimensions in the query and key vectors, enabling relative position
 * awareness without explicit position embeddings.
 *
 * DeepSeek R1 uses RoPE with configurable base theta and optional NTK-aware
 * scaling for extended context lengths.
 */

#pragma once

#include <cuda_runtime.h>

namespace llm {

/**
 * @brief RoPE configuration
 *
 * Controls the frequency computation and optional scaling for context
 * length extension via NTK-aware interpolation.
 */
struct RoPEConfig {
    float theta;          ///< Base frequency (default: 10000.0)
    int head_dim;         ///< Dimension per head (must be even)
    int max_seq_len;      ///< Maximum sequence length
    float ntk_alpha;      ///< NTK-aware scaling factor (1.0 = no scaling)

    /**
     * @brief Construct RoPE configuration
     *
     * @param theta       Base frequency for rotary embeddings
     * @param head_dim    Dimension per head (must be even for pair rotation)
     * @param max_seq_len Maximum sequence length
     * @param ntk_alpha   NTK scaling factor (default: 1.0, no scaling)
     */
    RoPEConfig(float theta = 10000.0f, int head_dim = 64,
               int max_seq_len = 4096, float ntk_alpha = 1.0f)
        : theta(theta), head_dim(head_dim),
          max_seq_len(max_seq_len), ntk_alpha(ntk_alpha) {}
};

/**
 * @brief Apply RoPE to query and key tensors in-place
 *
 * For each position p and dimension pair (2i, 2i+1):
 *   freq = 1.0 / (theta^(2i/head_dim))
 *   angle = p * freq
 *   q[2i]   = q[2i]*cos(angle) - q[2i+1]*sin(angle)
 *   q[2i+1] = q[2i]*sin(angle) + q[2i+1]*cos(angle)
 *
 * With NTK-aware scaling, theta is replaced by theta * alpha^(head_dim/(head_dim-2)).
 *
 * @param[in,out] Q        Query tensor [batch, seq_len, num_heads * head_dim]
 * @param[in,out] K        Key tensor [batch, seq_len, num_kv_heads * head_dim]
 * @param[in]     config   RoPE configuration
 * @param[in]     batch_size Number of sequences in batch
 * @param[in]     seq_len    Current sequence length
 * @param[in]     num_heads  Number of query heads
 * @param[in]     num_kv_heads Number of KV heads
 * @param[in]     pos_offset Position offset for KV-cache (default: 0)
 * @param[in]     stream     CUDA stream (default: 0)
 *
 * @note All pointers must be device memory
 * @pre head_dim must be even
 */
void rope_forward(float* Q, float* K,
                  const RoPEConfig& config,
                  int batch_size, int seq_len,
                  int num_heads, int num_kv_heads,
                  int pos_offset = 0,
                  cudaStream_t stream = 0);

/**
 * @brief Precompute RoPE frequency table
 *
 * Precomputes cos/sin tables for all positions up to max_seq_len, avoiding
 * redundant trigonometric computations during inference.
 *
 * @param[out] cos_table  Cosine values [max_seq_len, head_dim/2]
 * @param[out] sin_table  Sine values [max_seq_len, head_dim/2]
 * @param[in]  config     RoPE configuration
 * @param[in]  stream     CUDA stream (default: 0)
 */
void rope_precompute_freqs(float* cos_table, float* sin_table,
                           const RoPEConfig& config,
                           cudaStream_t stream = 0);

} // namespace llm
