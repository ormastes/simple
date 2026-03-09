/**
 * @file beam_search.cpp
 * @brief Beam search decoding and KV cache management for LLM inference
 *
 * Implements beam search: a breadth-first search strategy that maintains
 * the top-k highest-scoring partial sequences (beams) at each generation
 * step. Each beam is scored by cumulative log-probability. At each step,
 * all beams are expanded with every vocabulary token, scored, and pruned
 * back to the top-k candidates.
 *
 * Also provides the InferenceEngine class and KV cache allocation utilities.
 */

#include "common/inference_engine.h"
#include "common/gpt_model.h"
#include "common/text_generator.h"
#include <cuda_runtime.h>
#include <cstdio>
#include <cmath>
#include <vector>
#include <algorithm>
#include <limits>

namespace llm {

// ============================================================================
// Beam search helpers
// ============================================================================

/**
 * @brief Single beam hypothesis during search
 */
struct Beam {
    std::vector<int> tokens;  ///< Generated token sequence
    float score;              ///< Cumulative log probability
    bool finished;            ///< Whether EOS was generated

    bool operator<(const Beam& other) const {
        return score > other.score;  // Higher score = better (for sorting)
    }
};

/**
 * @brief Apply length normalization to beam score
 *
 * Normalizes by (5 + length)^alpha / (5 + 1)^alpha as in Wu et al. (2016).
 *
 * @param raw_score  Unnormalized cumulative log-probability
 * @param length     Sequence length
 * @param alpha      Length penalty exponent (default: 0.6)
 * @return Length-normalized score
 */
static float length_normalize(float raw_score, int length, float alpha = 0.6f) {
    float penalty = std::pow(5.0f + length, alpha) / std::pow(6.0f, alpha);
    return raw_score / penalty;
}

// ============================================================================
// InferenceEngine implementation
// ============================================================================

InferenceEngine::InferenceEngine(float* d_params, int num_layers, int d_model,
                                 int num_heads, int vocab_size, int max_seq_len)
    : d_params_(d_params), num_layers_(num_layers), d_model_(d_model),
      num_heads_(num_heads), head_dim_(d_model / num_heads),
      vocab_size_(vocab_size), max_seq_len_(max_seq_len) {
    kv_cache_ = {};
}

InferenceEngine::~InferenceEngine() {
    free_kv_cache(kv_cache_);
}

void InferenceEngine::allocate_kv_cache() {
    kv_cache_ = llm::allocate_kv_cache(num_layers_, max_seq_len_,
                                        num_heads_, head_dim_);
}

void InferenceEngine::reset_kv_cache() {
    kv_cache_.current_len = 0;
}

std::vector<int> InferenceEngine::generate(const std::vector<int>& prompt_ids,
                                            const GenerateConfig& config) {
    std::vector<int> output = prompt_ids;
    int current_len = static_cast<int>(prompt_ids.size());

    // Allocate device buffers
    int* d_input = nullptr;
    float* d_logits = nullptr;
    cudaMalloc(&d_input, max_seq_len_ * sizeof(int));
    cudaMalloc(&d_logits, vocab_size_ * sizeof(float));

    // Copy prompt to device
    cudaMemcpy(d_input, prompt_ids.data(), prompt_ids.size() * sizeof(int),
               cudaMemcpyHostToDevice);

    for (int step = 0; step < config.max_new_tokens; step++) {
        if (current_len >= max_seq_len_) break;

        // Get logits for the last position
        // (In a real implementation, this would call the model forward pass
        //  with KV cache; here we provide the scaffolding)
        std::vector<float> h_logits(vocab_size_);

        // Apply temperature
        if (config.temperature != 1.0f && config.temperature > 0.0f) {
            for (auto& l : h_logits) l /= config.temperature;
        }

        // Softmax
        float max_logit = *std::max_element(h_logits.begin(), h_logits.end());
        float sum_exp = 0.0f;
        for (auto& l : h_logits) {
            l = std::exp(l - max_logit);
            sum_exp += l;
        }
        for (auto& l : h_logits) l /= sum_exp;

        // Greedy selection (pick highest probability)
        int next_token = 0;
        if (config.strategy == DecodingStrategy::Greedy || config.top_k <= 0) {
            next_token = static_cast<int>(
                std::max_element(h_logits.begin(), h_logits.end()) - h_logits.begin());
        } else {
            // Top-k sampling: sort indices, keep top-k, sample
            std::vector<std::pair<float, int>> scored(vocab_size_);
            for (int i = 0; i < vocab_size_; i++) {
                scored[i] = {h_logits[i], i};
            }
            std::partial_sort(scored.begin(), scored.begin() + config.top_k,
                             scored.end(), std::greater<>());

            // Renormalize top-k
            float topk_sum = 0.0f;
            for (int i = 0; i < config.top_k; i++) topk_sum += scored[i].first;

            // Simple deterministic pick of the highest for scaffolding
            next_token = scored[0].second;
        }

        output.push_back(next_token);
        current_len++;

        if (next_token == config.eos_token_id) break;
    }

    cudaFree(d_input);
    cudaFree(d_logits);

    return output;
}

std::vector<int> InferenceEngine::beam_search(const std::vector<int>& prompt_ids,
                                               int beam_size, int max_length,
                                               int eos_token) {
    // Initialize beams
    std::vector<Beam> beams(1);
    beams[0].tokens = prompt_ids;
    beams[0].score = 0.0f;
    beams[0].finished = false;

    std::vector<Beam> completed;

    // Allocate device buffers for logits computation
    float* d_logits = nullptr;
    cudaMalloc(&d_logits, vocab_size_ * sizeof(float));

    for (int step = 0; step < max_length - static_cast<int>(prompt_ids.size()); step++) {
        std::vector<Beam> candidates;

        for (auto& beam : beams) {
            if (beam.finished) {
                candidates.push_back(beam);
                continue;
            }

            // In a full implementation, compute model forward pass for this beam.
            // Here we use placeholder logits for the scaffolding.
            std::vector<float> h_logits(vocab_size_, 0.0f);

            // Softmax to get log-probabilities
            float max_logit = *std::max_element(h_logits.begin(), h_logits.end());
            float sum_exp = 0.0f;
            for (float l : h_logits) sum_exp += std::exp(l - max_logit);

            // Expand beam with top-k tokens
            std::vector<std::pair<float, int>> scored(vocab_size_);
            for (int i = 0; i < vocab_size_; i++) {
                float log_prob = (h_logits[i] - max_logit) - std::log(sum_exp);
                scored[i] = {log_prob, i};
            }
            std::partial_sort(scored.begin(),
                             scored.begin() + std::min(beam_size, vocab_size_),
                             scored.end(), std::greater<>());

            for (int k = 0; k < beam_size && k < vocab_size_; k++) {
                Beam new_beam;
                new_beam.tokens = beam.tokens;
                new_beam.tokens.push_back(scored[k].second);
                new_beam.score = beam.score + scored[k].first;
                new_beam.finished = (scored[k].second == eos_token);

                if (new_beam.finished) {
                    completed.push_back(new_beam);
                } else {
                    candidates.push_back(new_beam);
                }
            }
        }

        // Keep top beam_size candidates
        std::sort(candidates.begin(), candidates.end());
        if (static_cast<int>(candidates.size()) > beam_size) {
            candidates.resize(beam_size);
        }
        beams = candidates;

        if (beams.empty()) break;
    }

    // Add unfinished beams to completed
    for (auto& beam : beams) {
        completed.push_back(beam);
    }

    cudaFree(d_logits);

    // Return the best sequence (highest length-normalized score)
    if (completed.empty()) return prompt_ids;

    float best_score = -std::numeric_limits<float>::infinity();
    int best_idx = 0;
    for (size_t i = 0; i < completed.size(); i++) {
        float normalized = length_normalize(completed[i].score,
                                            static_cast<int>(completed[i].tokens.size()));
        if (normalized > best_score) {
            best_score = normalized;
            best_idx = static_cast<int>(i);
        }
    }

    return completed[best_idx].tokens;
}

// ============================================================================
// KV cache allocation helpers
// ============================================================================

KVCache allocate_kv_cache(int num_layers, int max_seq_len,
                           int num_heads, int head_dim) {
    KVCache cache = {};
    cache.num_layers = num_layers;
    cache.max_seq_len = max_seq_len;
    cache.num_heads = num_heads;
    cache.head_dim = head_dim;
    cache.current_len = 0;

    size_t layer_size = static_cast<size_t>(max_seq_len) * num_heads * head_dim * sizeof(float);

    cudaMalloc(&cache.d_key_cache, static_cast<size_t>(num_layers) * layer_size);
    cudaMalloc(&cache.d_value_cache, static_cast<size_t>(num_layers) * layer_size);

    if (cache.d_key_cache) cudaMemset(cache.d_key_cache, 0, num_layers * layer_size);
    if (cache.d_value_cache) cudaMemset(cache.d_value_cache, 0, num_layers * layer_size);

    return cache;
}

void free_kv_cache(KVCache& cache) {
    if (cache.d_key_cache) {
        cudaFree(cache.d_key_cache);
        cache.d_key_cache = nullptr;
    }
    if (cache.d_value_cache) {
        cudaFree(cache.d_value_cache);
        cache.d_value_cache = nullptr;
    }
    cache.current_len = 0;
}

// ============================================================================
// generate_with_cache (free function using GPTModel and SamplingConfig)
// ============================================================================

void generate_with_cache(int* output_ids, GPTModel& model,
                        const int* prompt_ids, int prompt_len,
                        const SamplingConfig& sampling,
                        int max_seq_len,
                        cudaStream_t stream) {
    // Copy prompt to output
    cudaMemcpyAsync(output_ids, prompt_ids, prompt_len * sizeof(int),
                    cudaMemcpyDeviceToDevice, stream);

    int current_len = prompt_len;
    int max_len = std::min(max_seq_len,
                            prompt_len + sampling.max_new_tokens);

    // Allocate logits buffer
    float* d_logits = nullptr;
    cudaMalloc(&d_logits, static_cast<size_t>(model.config.vocab_size) * sizeof(float));

    for (int step = prompt_len; step < max_len; step++) {
        // Full forward pass (without KV cache optimization for now)
        // A full KV-cache implementation would only compute the new token
        float* d_full_logits = nullptr;
        cudaMalloc(&d_full_logits,
                   static_cast<size_t>(current_len) * model.config.vocab_size * sizeof(float));

        model.forward(d_full_logits, output_ids, 1, current_len, stream);

        // Extract logits for the last position
        size_t last_offset = static_cast<size_t>(current_len - 1) * model.config.vocab_size;
        cudaMemcpyAsync(d_logits, d_full_logits + last_offset,
                        model.config.vocab_size * sizeof(float),
                        cudaMemcpyDeviceToDevice, stream);

        // Sample next token using the sampling config
        gpu_top_k_sampling(output_ids + current_len, d_logits,
                          model.config.vocab_size, sampling.top_k,
                          sampling.temperature, stream);

        cudaFree(d_full_logits);
        current_len++;
    }

    cudaFree(d_logits);
}

} // namespace llm
