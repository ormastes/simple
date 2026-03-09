/**
 * @file text_generator.h
 * @brief Text generation with sampling strategies
 *
 * Provides GPU-accelerated sampling methods (top-k, top-p/nucleus) and
 * an autoregressive generation loop that uses a GPT model to produce
 * token sequences from a prompt.
 *
 * Based on "LLMs from Scratch" Chapter 5.
 */

#pragma once

#include <cuda_runtime.h>
#include "gpt_model.h"

namespace llm {

/**
 * @brief Configuration for text generation sampling
 *
 * Controls the sampling strategy used during autoregressive generation.
 * Supports temperature scaling, top-k filtering, and nucleus (top-p) sampling.
 */
struct SamplingConfig {
    float temperature;  ///< Sampling temperature (1.0 = normal, <1.0 = sharper, >1.0 = flatter)
    int top_k;         ///< Top-k sampling: keep only top-k logits (0 = disabled)
    float top_p;       ///< Nucleus sampling threshold (1.0 = disabled)
    int max_new_tokens; ///< Maximum number of tokens to generate

    /**
     * @brief Default sampling configuration
     *
     * Default values provide a good balance between quality and diversity.
     */
    SamplingConfig() : temperature(1.0f), top_k(50), top_p(0.9f), max_new_tokens(100) {}
};

/**
 * @brief GPU-accelerated top-k sampling
 *
 * Sorts logits, keeps only the top-k values, applies temperature scaling,
 * converts to probabilities via softmax, and samples one token.
 *
 * @param[out] output_token  Sampled token ID (device memory, single int)
 * @param[in]  logits        Raw logits for one position [vocab_size]
 * @param[in]  vocab_size    Size of vocabulary
 * @param[in]  top_k         Number of top candidates to keep
 * @param[in]  temperature   Temperature for scaling logits
 * @param[in]  stream        CUDA stream (default: 0)
 *
 * @note Uses a single block with shared memory; suitable for vocab_size up to ~65K
 */
void gpu_top_k_sampling(int* output_token, const float* logits, int vocab_size,
                       int top_k, float temperature, cudaStream_t stream = 0);

/**
 * @brief GPU-accelerated top-p (nucleus) sampling
 *
 * Sorts logits by probability, accumulates until the cumulative probability
 * exceeds top_p, masks remaining tokens, and samples from the nucleus.
 *
 * @param[out] output_token  Sampled token ID (device memory, single int)
 * @param[in]  logits        Raw logits for one position [vocab_size]
 * @param[in]  vocab_size    Size of vocabulary
 * @param[in]  top_p         Cumulative probability threshold
 * @param[in]  temperature   Temperature for scaling logits
 * @param[in]  stream        CUDA stream (default: 0)
 *
 * @note Uses a single block with shared memory; suitable for vocab_size up to ~65K
 */
void gpu_top_p_sampling(int* output_token, const float* logits, int vocab_size,
                       float top_p, float temperature, cudaStream_t stream = 0);

/**
 * @brief Generate tokens autoregressively
 *
 * Starting from a prompt, repeatedly runs the GPT model forward pass
 * to get logits for the last position, samples the next token, and
 * appends it to the sequence. Continues until max_new_tokens is reached.
 *
 * @param[out] output_ids  Output token IDs [prompt_len + max_new_tokens]
 * @param[in]  model       GPT model (must be allocated)
 * @param[in]  prompt_ids  Input prompt token IDs (device memory) [prompt_len]
 * @param[in]  prompt_len  Length of the prompt
 * @param[in]  config      Sampling configuration
 * @param[in]  stream      CUDA stream (default: 0)
 *
 * @note output_ids must be pre-allocated with at least (prompt_len + max_new_tokens) ints
 * @note The prompt is copied into the beginning of output_ids
 */
void generate(int* output_ids, GPTModel& model, const int* prompt_ids,
             int prompt_len, const SamplingConfig& config,
             cudaStream_t stream = 0);

} // namespace llm
