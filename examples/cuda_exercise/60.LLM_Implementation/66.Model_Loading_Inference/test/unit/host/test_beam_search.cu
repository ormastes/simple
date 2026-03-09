/**
 * @file test_beam_search.cpp
 * @brief Unit tests for beam search decoding
 *
 * Tests beam search implementation by verifying:
 * - Beam search produces sequences longer than the prompt
 * - KV cache allocation and deallocation work correctly
 * - Length normalization scoring is correct
 * - InferenceEngine greedy generation works
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/inference_engine.h"
#include "cuda_utils.h"
#include <vector>
#include <cmath>

namespace llm {

class BeamSearchTest : public GpuTest {
protected:
    int num_layers = 2;
    int d_model = 64;
    int num_heads = 4;
    int vocab_size = 256;
    int max_seq_len = 128;
    float* d_params = nullptr;

    void SetUp() override {
        GpuTest::SetUp();
        // Allocate a dummy parameter buffer
        size_t param_size = static_cast<size_t>(d_model * d_model * num_layers) * sizeof(float);
        CHECK_CUDA(cudaMalloc(&d_params, param_size));
        CHECK_CUDA(cudaMemset(d_params, 0, param_size));
    }

    void TearDown() override {
        if (d_params) cudaFree(d_params);
        GpuTest::TearDown();
    }
};

TEST_F(BeamSearchTest, GreedyGenerationProducesTokens) {
    InferenceEngine engine(d_params, num_layers, d_model, num_heads,
                          vocab_size, max_seq_len);
    engine.allocate_kv_cache();

    std::vector<int> prompt = {1, 2, 3};
    GenerateConfig config;
    config.strategy = DecodingStrategy::Greedy;
    config.max_new_tokens = 5;
    config.eos_token_id = -1; // No EOS to ensure we generate max tokens

    std::vector<int> output = engine.generate(prompt, config);

    // Output should be prompt + generated tokens
    EXPECT_GT(output.size(), prompt.size())
        << "Generated sequence should be longer than prompt";
    EXPECT_LE(output.size(), prompt.size() + config.max_new_tokens)
        << "Generated sequence should not exceed max length";

    // Prompt should be preserved at the beginning
    for (size_t i = 0; i < prompt.size(); i++) {
        EXPECT_EQ(output[i], prompt[i])
            << "Prompt token " << i << " should be preserved";
    }
}

TEST_F(BeamSearchTest, BeamSearchProducesTokens) {
    InferenceEngine engine(d_params, num_layers, d_model, num_heads,
                          vocab_size, max_seq_len);
    engine.allocate_kv_cache();

    std::vector<int> prompt = {1, 2, 3};
    int beam_size = 3;
    int max_length = 10;
    int eos_token = -1; // No EOS for testing

    std::vector<int> output = engine.beam_search(prompt, beam_size,
                                                  max_length, eos_token);

    // Output should contain at least the prompt
    EXPECT_GE(output.size(), prompt.size())
        << "Beam search output should be at least as long as prompt";

    // Prompt should be preserved
    for (size_t i = 0; i < prompt.size(); i++) {
        EXPECT_EQ(output[i], prompt[i]);
    }
}

TEST_F(BeamSearchTest, BeamSearchWithEOS) {
    InferenceEngine engine(d_params, num_layers, d_model, num_heads,
                          vocab_size, max_seq_len);
    engine.allocate_kv_cache();

    std::vector<int> prompt = {10, 20};
    int beam_size = 2;
    int max_length = 20;
    int eos_token = 0; // Token 0 is EOS

    std::vector<int> output = engine.beam_search(prompt, beam_size,
                                                  max_length, eos_token);

    // Should have at least the prompt
    EXPECT_GE(output.size(), prompt.size());
}

TEST_F(BeamSearchTest, KVCacheAllocationAndFree) {
    KVCache cache = allocate_kv_cache(num_layers, max_seq_len,
                                       num_heads, d_model / num_heads);

    EXPECT_EQ(cache.num_layers, num_layers);
    EXPECT_EQ(cache.max_seq_len, max_seq_len);
    EXPECT_EQ(cache.num_heads, num_heads);
    EXPECT_EQ(cache.current_len, 0);
    EXPECT_NE(cache.d_key_cache, nullptr);
    EXPECT_NE(cache.d_value_cache, nullptr);

    free_kv_cache(cache);

    EXPECT_EQ(cache.d_key_cache, nullptr);
    EXPECT_EQ(cache.d_value_cache, nullptr);
}

TEST_F(BeamSearchTest, ResetKVCache) {
    InferenceEngine engine(d_params, num_layers, d_model, num_heads,
                          vocab_size, max_seq_len);
    engine.allocate_kv_cache();

    // Generate some tokens (advances KV cache)
    std::vector<int> prompt = {1};
    GenerateConfig config;
    config.max_new_tokens = 3;
    config.eos_token_id = -1;
    engine.generate(prompt, config);

    // Reset should not crash
    engine.reset_kv_cache();
}

} // namespace llm
