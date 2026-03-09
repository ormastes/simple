/**
 * @file text_generator.cu
 * @brief Autoregressive text generation loop
 *
 * Implements the generate() function that autoregressively produces tokens
 * by repeatedly calling the GPT model forward pass and sampling the next
 * token from the output logits.
 */

#include "common/text_generator.h"
#include "cuda_utils.h"

namespace llm {

void generate(int* output_ids, GPTModel& model, const int* prompt_ids,
             int prompt_len, const SamplingConfig& config,
             cudaStream_t stream) {
    int vocab_size = model.config.vocab_size;
    int max_seq_len = model.config.max_seq_len;
    int total_len = prompt_len + config.max_new_tokens;

    // Clamp total length to max_seq_len
    if (total_len > max_seq_len) {
        total_len = max_seq_len;
    }

    // Copy prompt to the beginning of output_ids
    CHECK_CUDA(cudaMemcpyAsync(output_ids, prompt_ids,
                                prompt_len * sizeof(int),
                                cudaMemcpyDeviceToDevice, stream));
    CHECK_CUDA(cudaStreamSynchronize(stream));

    // Allocate logits buffer for forward pass (batch_size=1)
    // logits shape: [1, current_seq_len, vocab_size]
    // We only need the logits for the last position
    float* logits = nullptr;
    int* next_token = nullptr;

    // We allocate for the maximum sequence length we'll process
    size_t max_logits_size = (size_t)total_len * vocab_size;
    CHECK_CUDA(cudaMalloc(&logits, max_logits_size * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&next_token, sizeof(int)));

    // Autoregressive generation loop
    for (int step = 0; step < config.max_new_tokens; ++step) {
        int current_len = prompt_len + step;

        // Clamp to max_seq_len
        if (current_len >= max_seq_len) {
            break;
        }

        // Forward pass with batch_size=1, seq_len=current_len
        // This re-computes the full sequence each time (no KV cache)
        model.forward(logits, output_ids, 1, current_len, stream);
        CHECK_CUDA(cudaStreamSynchronize(stream));

        // Get logits for the last position: logits[(current_len-1) * vocab_size]
        const float* last_logits = logits + (size_t)(current_len - 1) * vocab_size;

        // Sample next token based on configuration
        if (config.top_k > 0 && config.top_k < vocab_size) {
            gpu_top_k_sampling(next_token, last_logits, vocab_size,
                             config.top_k, config.temperature, stream);
        } else {
            gpu_top_p_sampling(next_token, last_logits, vocab_size,
                             config.top_p, config.temperature, stream);
        }
        CHECK_CUDA(cudaStreamSynchronize(stream));

        // Append the sampled token to output_ids
        CHECK_CUDA(cudaMemcpyAsync(output_ids + current_len, next_token,
                                    sizeof(int), cudaMemcpyDeviceToDevice, stream));
        CHECK_CUDA(cudaStreamSynchronize(stream));
    }

    // Free temporary buffers
    cuda_free(logits);
    cuda_free(next_token);
}

} // namespace llm
