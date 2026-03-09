/**
 * @file inference_engine.h
 * @brief Inference engine for LLM text generation
 *
 * Provides the InferenceEngine class that orchestrates autoregressive
 * text generation with KV-cache for efficient decoding. Supports
 * greedy decoding, top-k sampling, and beam search strategies.
 */

#ifndef INFERENCE_ENGINE_H
#define INFERENCE_ENGINE_H

#include <cuda_runtime.h>
#include <string>
#include <vector>
#include <cstdint>

namespace llm {

/**
 * @brief Decoding strategy for text generation
 */
enum class DecodingStrategy {
    Greedy,     ///< Always pick the highest probability token
    TopK,       ///< Sample from top-k highest probability tokens
    TopP,       ///< Nucleus sampling: sample from smallest set with cumulative prob >= p
    BeamSearch  ///< Maintain multiple hypotheses and select the best
};

/**
 * @brief Configuration for text generation
 *
 * Controls all aspects of the generation process including decoding
 * strategy, sampling parameters, and stopping criteria.
 */
struct GenerateConfig {
    DecodingStrategy strategy;  ///< Decoding strategy
    int max_new_tokens;         ///< Maximum number of tokens to generate
    float temperature;          ///< Sampling temperature (1.0 = no change)
    int top_k;                  ///< Top-k sampling parameter (0 = disabled)
    float top_p;                ///< Nucleus sampling threshold (1.0 = disabled)
    int beam_size;              ///< Number of beams for beam search
    int eos_token_id;           ///< End-of-sequence token ID for stopping
    int pad_token_id;           ///< Padding token ID

    /**
     * @brief Construct generation config with defaults for greedy decoding
     */
    GenerateConfig()
        : strategy(DecodingStrategy::Greedy),
          max_new_tokens(256),
          temperature(1.0f),
          top_k(0),
          top_p(1.0f),
          beam_size(1),
          eos_token_id(50256),
          pad_token_id(50256) {}
};

/**
 * @brief KV-cache state for efficient autoregressive generation
 *
 * Stores cached key and value tensors from previous positions so they
 * don't need to be recomputed at each generation step. Each layer
 * maintains its own K and V cache.
 */
struct KVCache {
    float* d_key_cache;    ///< Key cache [num_layers, max_seq_len, num_heads, head_dim]
    float* d_value_cache;  ///< Value cache [num_layers, max_seq_len, num_heads, head_dim]
    int num_layers;        ///< Number of transformer layers
    int max_seq_len;       ///< Maximum sequence length
    int num_heads;         ///< Number of attention heads
    int head_dim;          ///< Dimension per attention head
    int current_len;       ///< Current number of cached positions
};

/**
 * @brief Beam hypothesis for beam search
 *
 * Represents a single candidate sequence in beam search, tracking
 * the generated token IDs and cumulative log-probability score.
 */
struct BeamHypothesis {
    std::vector<int> token_ids;  ///< Generated token sequence
    float score;                 ///< Cumulative log-probability score
    bool finished;               ///< Whether EOS has been generated
};

/**
 * @brief Inference engine for LLM text generation
 *
 * Manages the complete inference pipeline: prompt encoding, KV-cache
 * initialization, and autoregressive token generation with configurable
 * decoding strategies.
 */
class InferenceEngine {
public:
    /**
     * @brief Construct inference engine
     *
     * @param d_params     Model parameters (device)
     * @param num_layers   Number of transformer layers
     * @param d_model      Model dimension
     * @param num_heads    Number of attention heads
     * @param vocab_size   Vocabulary size
     * @param max_seq_len  Maximum sequence length
     */
    InferenceEngine(float* d_params, int num_layers, int d_model,
                    int num_heads, int vocab_size, int max_seq_len);

    ~InferenceEngine();

    /**
     * @brief Generate tokens from a prompt
     *
     * Processes the prompt through the model, then autoregressively
     * generates new tokens using the specified decoding strategy.
     * Uses KV-cache for efficient decoding.
     *
     * @param prompt_ids  Input prompt token IDs
     * @param config      Generation configuration
     * @return Generated token IDs (including prompt)
     */
    std::vector<int> generate(const std::vector<int>& prompt_ids,
                              const GenerateConfig& config);

    /**
     * @brief Generate tokens using beam search
     *
     * Maintains multiple candidate sequences (beams) and expands the
     * most promising ones at each step. Returns the highest-scoring
     * complete sequence.
     *
     * @param prompt_ids  Input prompt token IDs
     * @param beam_size   Number of beams to maintain
     * @param max_length  Maximum total sequence length
     * @param eos_token   End-of-sequence token ID
     * @return Best sequence from beam search
     */
    std::vector<int> beam_search(const std::vector<int>& prompt_ids,
                                 int beam_size, int max_length,
                                 int eos_token);

    /**
     * @brief Allocate KV-cache for inference
     *
     * Allocates device memory for key and value caches across all layers.
     * Must be called before generate() or beam_search().
     */
    void allocate_kv_cache();

    /**
     * @brief Reset KV-cache state
     *
     * Clears the cached keys and values, resetting current_len to 0.
     * Call between generating different sequences.
     */
    void reset_kv_cache();

private:
    float* d_params_;       ///< Model parameters (device, not owned)
    int num_layers_;        ///< Number of transformer layers
    int d_model_;           ///< Model dimension
    int num_heads_;         ///< Number of attention heads
    int head_dim_;          ///< Per-head dimension
    int vocab_size_;        ///< Vocabulary size
    int max_seq_len_;       ///< Maximum sequence length
    KVCache kv_cache_;      ///< KV-cache for efficient decoding
};

/**
 * @brief Allocate KV-cache buffers on GPU
 *
 * @param num_layers   Number of transformer layers
 * @param max_seq_len  Maximum sequence length
 * @param num_heads    Number of attention heads
 * @param head_dim     Per-head dimension
 * @return Allocated KVCache with zeroed buffers
 */
KVCache allocate_kv_cache(int num_layers, int max_seq_len,
                          int num_heads, int head_dim);

/**
 * @brief Free KV-cache buffers
 *
 * @param cache Cache to free; pointers nulled after freeing
 */
void free_kv_cache(KVCache& cache);

} // namespace llm

#endif // INFERENCE_ENGINE_H
