/**
 * @file test_sampling.cu
 * @brief Unit tests for GPU sampling strategies (top-k and top-p)
 *
 * Verifies that sampling produces valid token indices and respects
 * the configured constraints (top-k count, top-p threshold).
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/text_generator.h"
#include "cuda_utils.h"
#include <vector>
#include <set>
#include <cmath>

using namespace llm;

/**
 * @brief Test fixture for sampling tests with GPU setup
 */
class SamplingTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }
};

/**
 * @brief Test top-k sampling produces valid token indices
 */
TEST_F(SamplingTest, TopK_ValidTokenIndex) {
    const int vocab_size = 64;
    const int top_k = 10;
    const float temperature = 1.0f;

    // Create logits with a clear distribution
    std::vector<float> h_logits(vocab_size);
    for (int i = 0; i < vocab_size; ++i) {
        h_logits[i] = -10.0f + static_cast<float>(i) * 0.3f;
    }

    float* d_logits = cuda_malloc<float>(vocab_size);
    CHECK_CUDA(cudaMemcpy(d_logits, h_logits.data(),
                         vocab_size * sizeof(float),
                         cudaMemcpyHostToDevice));

    int* d_output = cuda_malloc<int>(1);
    CHECK_CUDA(cudaMemset(d_output, 0, sizeof(int)));

    // Run top-k sampling multiple times
    for (int trial = 0; trial < 20; ++trial) {
        gpu_top_k_sampling(d_output, d_logits, vocab_size,
                          top_k, temperature);
        CHECK_CUDA(cudaDeviceSynchronize());

        int h_token = -1;
        CHECK_CUDA(cudaMemcpy(&h_token, d_output, sizeof(int),
                             cudaMemcpyDeviceToHost));

        // Token must be a valid index
        EXPECT_GE(h_token, 0) << "Token index is negative at trial " << trial;
        EXPECT_LT(h_token, vocab_size)
            << "Token index exceeds vocab_size at trial " << trial;
    }

    cuda_free(d_logits);
    cuda_free(d_output);
}

/**
 * @brief Test top-k sampling favors high-probability tokens
 */
TEST_F(SamplingTest, TopK_FavorsHighProbability) {
    const int vocab_size = 32;
    const int top_k = 3;
    const float temperature = 0.1f;  // Low temperature = sharper distribution

    // Create logits where token 20 has much higher logit
    std::vector<float> h_logits(vocab_size, -10.0f);
    h_logits[20] = 10.0f;
    h_logits[21] = 5.0f;
    h_logits[22] = 3.0f;

    float* d_logits = cuda_malloc<float>(vocab_size);
    CHECK_CUDA(cudaMemcpy(d_logits, h_logits.data(),
                         vocab_size * sizeof(float),
                         cudaMemcpyHostToDevice));

    int* d_output = cuda_malloc<int>(1);
    CHECK_CUDA(cudaMemset(d_output, 0, sizeof(int)));

    std::set<int> seen_tokens;
    int count_token_20 = 0;
    const int num_trials = 50;

    for (int trial = 0; trial < num_trials; ++trial) {
        gpu_top_k_sampling(d_output, d_logits, vocab_size,
                          top_k, temperature);
        CHECK_CUDA(cudaDeviceSynchronize());

        int h_token;
        CHECK_CUDA(cudaMemcpy(&h_token, d_output, sizeof(int),
                             cudaMemcpyDeviceToHost));

        EXPECT_GE(h_token, 0);
        EXPECT_LT(h_token, vocab_size);

        seen_tokens.insert(h_token);
        if (h_token == 20) count_token_20++;
    }

    // With very low temperature and token 20 having the highest logit,
    // it should be sampled most of the time
    EXPECT_GT(count_token_20, num_trials / 2)
        << "Token 20 should be sampled frequently with low temperature";

    std::cout << "Token 20 sampled " << count_token_20 << "/" << num_trials
              << " times" << std::endl;
    std::cout << "Unique tokens seen: " << seen_tokens.size() << std::endl;

    cuda_free(d_logits);
    cuda_free(d_output);
}

/**
 * @brief Test top-p sampling produces valid token indices
 */
TEST_F(SamplingTest, TopP_ValidTokenIndex) {
    const int vocab_size = 64;
    const float top_p = 0.9f;
    const float temperature = 1.0f;

    // Create logits with uniform-ish distribution
    std::vector<float> h_logits(vocab_size);
    for (int i = 0; i < vocab_size; ++i) {
        h_logits[i] = static_cast<float>(i % 10) * 0.5f;
    }

    float* d_logits = cuda_malloc<float>(vocab_size);
    CHECK_CUDA(cudaMemcpy(d_logits, h_logits.data(),
                         vocab_size * sizeof(float),
                         cudaMemcpyHostToDevice));

    int* d_output = cuda_malloc<int>(1);
    CHECK_CUDA(cudaMemset(d_output, 0, sizeof(int)));

    for (int trial = 0; trial < 20; ++trial) {
        gpu_top_p_sampling(d_output, d_logits, vocab_size,
                          top_p, temperature);
        CHECK_CUDA(cudaDeviceSynchronize());

        int h_token;
        CHECK_CUDA(cudaMemcpy(&h_token, d_output, sizeof(int),
                             cudaMemcpyDeviceToHost));

        EXPECT_GE(h_token, 0) << "Token index is negative at trial " << trial;
        EXPECT_LT(h_token, vocab_size)
            << "Token index exceeds vocab_size at trial " << trial;
    }

    cuda_free(d_logits);
    cuda_free(d_output);
}

/**
 * @brief Test top-p sampling favors high-probability tokens
 */
TEST_F(SamplingTest, TopP_FavorsHighProbability) {
    const int vocab_size = 32;
    const float top_p = 0.5f;
    const float temperature = 0.1f;

    // One dominant token
    std::vector<float> h_logits(vocab_size, -10.0f);
    h_logits[15] = 10.0f;

    float* d_logits = cuda_malloc<float>(vocab_size);
    CHECK_CUDA(cudaMemcpy(d_logits, h_logits.data(),
                         vocab_size * sizeof(float),
                         cudaMemcpyHostToDevice));

    int* d_output = cuda_malloc<int>(1);
    CHECK_CUDA(cudaMemset(d_output, 0, sizeof(int)));

    int count_token_15 = 0;
    const int num_trials = 30;

    for (int trial = 0; trial < num_trials; ++trial) {
        gpu_top_p_sampling(d_output, d_logits, vocab_size,
                          top_p, temperature);
        CHECK_CUDA(cudaDeviceSynchronize());

        int h_token;
        CHECK_CUDA(cudaMemcpy(&h_token, d_output, sizeof(int),
                             cudaMemcpyDeviceToHost));

        if (h_token == 15) count_token_15++;
    }

    // With very low temperature and one dominant token, it should almost always be sampled
    EXPECT_GT(count_token_15, num_trials / 2)
        << "Dominant token should be sampled frequently";

    std::cout << "Token 15 sampled " << count_token_15 << "/" << num_trials
              << " times" << std::endl;

    cuda_free(d_logits);
    cuda_free(d_output);
}

/**
 * @brief Test top-k sampling with k=1 always returns the argmax
 */
TEST_F(SamplingTest, TopK_K1_IsArgmax) {
    const int vocab_size = 16;
    const int top_k = 1;
    const float temperature = 1.0f;

    // Token 7 has the highest logit
    std::vector<float> h_logits(vocab_size, 0.0f);
    h_logits[7] = 100.0f;

    float* d_logits = cuda_malloc<float>(vocab_size);
    CHECK_CUDA(cudaMemcpy(d_logits, h_logits.data(),
                         vocab_size * sizeof(float),
                         cudaMemcpyHostToDevice));

    int* d_output = cuda_malloc<int>(1);
    CHECK_CUDA(cudaMemset(d_output, 0, sizeof(int)));

    for (int trial = 0; trial < 10; ++trial) {
        gpu_top_k_sampling(d_output, d_logits, vocab_size,
                          top_k, temperature);
        CHECK_CUDA(cudaDeviceSynchronize());

        int h_token;
        CHECK_CUDA(cudaMemcpy(&h_token, d_output, sizeof(int),
                             cudaMemcpyDeviceToHost));

        EXPECT_EQ(h_token, 7) << "Top-1 sampling should always return argmax";
    }

    cuda_free(d_logits);
    cuda_free(d_output);
}

/**
 * @brief Test sampling with temperature scaling
 */
TEST_F(SamplingTest, TemperatureEffect) {
    const int vocab_size = 16;
    const int top_k = vocab_size;

    // Moderately peaked distribution
    std::vector<float> h_logits(vocab_size);
    for (int i = 0; i < vocab_size; ++i) {
        h_logits[i] = static_cast<float>(i);
    }

    float* d_logits = cuda_malloc<float>(vocab_size);
    CHECK_CUDA(cudaMemcpy(d_logits, h_logits.data(),
                         vocab_size * sizeof(float),
                         cudaMemcpyHostToDevice));

    int* d_output = cuda_malloc<int>(1);
    CHECK_CUDA(cudaMemset(d_output, 0, sizeof(int)));

    // Low temperature should concentrate on top tokens
    std::set<int> low_temp_tokens;
    for (int trial = 0; trial < 30; ++trial) {
        gpu_top_k_sampling(d_output, d_logits, vocab_size,
                          top_k, 0.01f);  // Very low temperature
        CHECK_CUDA(cudaDeviceSynchronize());

        int h_token;
        CHECK_CUDA(cudaMemcpy(&h_token, d_output, sizeof(int),
                             cudaMemcpyDeviceToHost));
        low_temp_tokens.insert(h_token);
    }

    // With very low temperature, should mostly see the top token
    EXPECT_LE((int)low_temp_tokens.size(), 3)
        << "Low temperature should produce few unique tokens";

    std::cout << "Low temperature unique tokens: " << low_temp_tokens.size() << std::endl;

    cuda_free(d_logits);
    cuda_free(d_output);
}
