/**
 * @file test_text_generator.cu
 * @brief Unit tests for autoregressive text generation
 *
 * Tests the generate() function to verify it produces output sequences
 * of expected length with valid token IDs.
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/text_generator.h"
#include "cuda_utils.h"
#include <vector>

using namespace llm;

/**
 * @brief Test fixture for text generation tests with GPU setup
 */
class TextGeneratorTest : public GpuTest {
protected:
    GPTModel model;

    void SetUp() override {
        GpuTest::SetUp();
        model.config = gpt_tiny();
        model.allocate();
    }

    void TearDown() override {
        model.deallocate();
        GpuTest::TearDown();
    }
};

/**
 * @brief Test that generation produces output of expected length
 */
TEST_F(TextGeneratorTest, OutputLength) {
    int prompt_len = 4;
    int max_new_tokens = 8;
    int total_len = prompt_len + max_new_tokens;
    int vocab_size = model.config.vocab_size;

    // Create prompt
    std::vector<int> h_prompt = {1, 2, 3, 4};
    int* d_prompt = cuda_malloc<int>(prompt_len);
    CHECK_CUDA(cudaMemcpy(d_prompt, h_prompt.data(),
                         prompt_len * sizeof(int),
                         cudaMemcpyHostToDevice));

    // Allocate output buffer
    int* d_output = cuda_malloc<int>(total_len);
    CHECK_CUDA(cudaMemset(d_output, 0, total_len * sizeof(int)));

    // Configure sampling
    SamplingConfig config;
    config.max_new_tokens = max_new_tokens;
    config.temperature = 1.0f;
    config.top_k = 10;

    // Generate
    generate(d_output, model, d_prompt, prompt_len, config);
    CHECK_CUDA(cudaDeviceSynchronize());

    // Copy output to host
    std::vector<int> h_output(total_len);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output,
                         total_len * sizeof(int),
                         cudaMemcpyDeviceToHost));

    // Verify prompt is preserved at the beginning
    for (int i = 0; i < prompt_len; ++i) {
        EXPECT_EQ(h_output[i], h_prompt[i])
            << "Prompt token " << i << " was modified";
    }

    // Verify generated tokens are valid indices
    for (int i = prompt_len; i < total_len; ++i) {
        EXPECT_GE(h_output[i], 0)
            << "Generated token " << i << " is negative";
        EXPECT_LT(h_output[i], vocab_size)
            << "Generated token " << i << " exceeds vocab_size";
    }

    std::cout << "Generated sequence: ";
    for (int i = 0; i < total_len; ++i) {
        std::cout << h_output[i] << " ";
    }
    std::cout << std::endl;

    cuda_free(d_prompt);
    cuda_free(d_output);
}

/**
 * @brief Test generation with single-token prompt
 */
TEST_F(TextGeneratorTest, SingleTokenPrompt) {
    int prompt_len = 1;
    int max_new_tokens = 5;
    int total_len = prompt_len + max_new_tokens;
    int vocab_size = model.config.vocab_size;

    int h_prompt = 0;
    int* d_prompt = cuda_malloc<int>(1);
    CHECK_CUDA(cudaMemcpy(d_prompt, &h_prompt, sizeof(int),
                         cudaMemcpyHostToDevice));

    int* d_output = cuda_malloc<int>(total_len);
    CHECK_CUDA(cudaMemset(d_output, 0, total_len * sizeof(int)));

    SamplingConfig config;
    config.max_new_tokens = max_new_tokens;
    config.top_k = 5;

    generate(d_output, model, d_prompt, prompt_len, config);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<int> h_output(total_len);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output,
                         total_len * sizeof(int),
                         cudaMemcpyDeviceToHost));

    // First token should be the prompt
    EXPECT_EQ(h_output[0], 0);

    // All tokens should be valid
    for (int i = 0; i < total_len; ++i) {
        EXPECT_GE(h_output[i], 0);
        EXPECT_LT(h_output[i], vocab_size);
    }

    cuda_free(d_prompt);
    cuda_free(d_output);
}

/**
 * @brief Test generation with top-p sampling
 */
TEST_F(TextGeneratorTest, TopPSampling) {
    int prompt_len = 3;
    int max_new_tokens = 4;
    int total_len = prompt_len + max_new_tokens;
    int vocab_size = model.config.vocab_size;

    std::vector<int> h_prompt = {10, 20, 30};
    int* d_prompt = cuda_malloc<int>(prompt_len);
    CHECK_CUDA(cudaMemcpy(d_prompt, h_prompt.data(),
                         prompt_len * sizeof(int),
                         cudaMemcpyHostToDevice));

    int* d_output = cuda_malloc<int>(total_len);
    CHECK_CUDA(cudaMemset(d_output, 0, total_len * sizeof(int)));

    // Use top-p sampling (disable top-k by setting it to 0)
    SamplingConfig config;
    config.max_new_tokens = max_new_tokens;
    config.top_k = 0;
    config.top_p = 0.9f;
    config.temperature = 1.0f;

    generate(d_output, model, d_prompt, prompt_len, config);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<int> h_output(total_len);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output,
                         total_len * sizeof(int),
                         cudaMemcpyDeviceToHost));

    // Verify prompt preservation
    for (int i = 0; i < prompt_len; ++i) {
        EXPECT_EQ(h_output[i], h_prompt[i]);
    }

    // Verify valid token IDs
    for (int i = prompt_len; i < total_len; ++i) {
        EXPECT_GE(h_output[i], 0);
        EXPECT_LT(h_output[i], vocab_size);
    }

    cuda_free(d_prompt);
    cuda_free(d_output);
}

/**
 * @brief Test that different prompts produce different outputs
 */
TEST_F(TextGeneratorTest, DifferentPromptsProduceDifferentOutputs) {
    int prompt_len = 2;
    int max_new_tokens = 4;
    int total_len = prompt_len + max_new_tokens;

    std::vector<int> h_prompt1 = {1, 2};
    std::vector<int> h_prompt2 = {100, 200};

    int* d_prompt1 = cuda_malloc<int>(prompt_len);
    int* d_prompt2 = cuda_malloc<int>(prompt_len);
    int* d_output1 = cuda_malloc<int>(total_len);
    int* d_output2 = cuda_malloc<int>(total_len);

    CHECK_CUDA(cudaMemcpy(d_prompt1, h_prompt1.data(),
                         prompt_len * sizeof(int), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_prompt2, h_prompt2.data(),
                         prompt_len * sizeof(int), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemset(d_output1, 0, total_len * sizeof(int)));
    CHECK_CUDA(cudaMemset(d_output2, 0, total_len * sizeof(int)));

    SamplingConfig config;
    config.max_new_tokens = max_new_tokens;
    config.top_k = 1;  // Greedy to make deterministic
    config.temperature = 1.0f;

    generate(d_output1, model, d_prompt1, prompt_len, config);
    generate(d_output2, model, d_prompt2, prompt_len, config);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<int> h_output1(total_len), h_output2(total_len);
    CHECK_CUDA(cudaMemcpy(h_output1.data(), d_output1,
                         total_len * sizeof(int), cudaMemcpyDeviceToHost));
    CHECK_CUDA(cudaMemcpy(h_output2.data(), d_output2,
                         total_len * sizeof(int), cudaMemcpyDeviceToHost));

    // Different prompts should produce different outputs (at least in the prompt part)
    bool any_different = false;
    for (int i = 0; i < total_len; ++i) {
        if (h_output1[i] != h_output2[i]) {
            any_different = true;
            break;
        }
    }

    EXPECT_TRUE(any_different)
        << "Different prompts produced identical outputs";

    std::cout << "Output 1: ";
    for (int i = 0; i < total_len; ++i) std::cout << h_output1[i] << " ";
    std::cout << std::endl;
    std::cout << "Output 2: ";
    for (int i = 0; i < total_len; ++i) std::cout << h_output2[i] << " ";
    std::cout << std::endl;

    cuda_free(d_prompt1);
    cuda_free(d_prompt2);
    cuda_free(d_output1);
    cuda_free(d_output2);
}
