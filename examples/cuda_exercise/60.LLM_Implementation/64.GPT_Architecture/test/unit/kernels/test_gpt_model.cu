/**
 * @file test_gpt_model.cu
 * @brief Unit tests for GPT model forward pass
 *
 * Tests model allocation, parameter counting, forward pass output shape,
 * and basic numerical properties using the gpt_tiny() configuration.
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/gpt_model.h"
#include "cuda_utils.h"
#include <vector>
#include <cmath>

using namespace llm;

/**
 * @brief Test fixture for GPT model tests with GPU setup
 */
class GPTModelTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }
};

/**
 * @brief Test parameter counting for known GPT configurations
 */
TEST_F(GPTModelTest, ParameterCounting) {
    // GPT-2 Small should have ~124M parameters
    GPTConfig small = gpt2_small();
    long long small_params = count_parameters(small);
    // Expected: ~124M (the exact count depends on weight tying)
    EXPECT_GT(small_params, 100000000LL);
    EXPECT_LT(small_params, 200000000LL);

    // GPT-2 Medium should have ~355M parameters
    GPTConfig medium = gpt2_medium();
    long long medium_params = count_parameters(medium);
    EXPECT_GT(medium_params, 300000000LL);
    EXPECT_LT(medium_params, 500000000LL);

    // Tiny config should have much fewer parameters
    GPTConfig tiny = gpt_tiny();
    long long tiny_params = count_parameters(tiny);
    EXPECT_GT(tiny_params, 0LL);
    EXPECT_LT(tiny_params, 1000000LL);  // Less than 1M

    std::cout << "GPT-2 Small params:  " << small_params << std::endl;
    std::cout << "GPT-2 Medium params: " << medium_params << std::endl;
    std::cout << "GPT Tiny params:     " << tiny_params << std::endl;
}

/**
 * @brief Test model allocation and deallocation
 */
TEST_F(GPTModelTest, AllocateAndDeallocate) {
    GPTModel model;
    model.config = gpt_tiny();

    // Allocate should not throw
    ASSERT_NO_FATAL_FAILURE(model.allocate());

    // Verify parameter count matches config
    EXPECT_EQ(model.num_parameters(), count_parameters(model.config));

    // Deallocate should not throw
    ASSERT_NO_FATAL_FAILURE(model.deallocate());
}

/**
 * @brief Test forward pass output shape with tiny config
 */
TEST_F(GPTModelTest, ForwardOutputShape) {
    GPTModel model;
    model.config = gpt_tiny();
    model.allocate();

    int batch_size = 2;
    int seq_len = 8;
    int vocab_size = model.config.vocab_size;

    // Create input token IDs
    std::vector<int> h_input(batch_size * seq_len);
    for (int i = 0; i < batch_size * seq_len; ++i) {
        h_input[i] = i % vocab_size;
    }

    int* d_input = cuda_malloc<int>(batch_size * seq_len);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(),
                         h_input.size() * sizeof(int),
                         cudaMemcpyHostToDevice));

    // Allocate logits output
    size_t logits_size = (size_t)batch_size * seq_len * vocab_size;
    float* d_logits = cuda_malloc<float>(logits_size);

    // Forward pass
    model.forward(d_logits, d_input, batch_size, seq_len);
    CHECK_CUDA(cudaDeviceSynchronize());

    // Copy logits to host
    std::vector<float> h_logits(logits_size);
    CHECK_CUDA(cudaMemcpy(h_logits.data(), d_logits,
                         logits_size * sizeof(float),
                         cudaMemcpyDeviceToHost));

    // Verify output is finite (no NaN or Inf)
    int finite_count = 0;
    int nan_count = 0;
    for (size_t i = 0; i < logits_size; ++i) {
        if (std::isfinite(h_logits[i])) {
            finite_count++;
        }
        if (std::isnan(h_logits[i])) {
            nan_count++;
        }
    }

    EXPECT_EQ(nan_count, 0) << "Forward pass produced NaN values";
    EXPECT_EQ(finite_count, (int)logits_size) << "Not all logits are finite";

    // Verify logits have non-trivial values (not all zeros)
    float max_abs = 0.0f;
    for (size_t i = 0; i < logits_size; ++i) {
        max_abs = std::max(max_abs, std::abs(h_logits[i]));
    }
    EXPECT_GT(max_abs, 0.0f) << "All logits are zero";

    std::cout << "Logits shape: [" << batch_size << ", " << seq_len
              << ", " << vocab_size << "]" << std::endl;
    std::cout << "Max absolute logit value: " << max_abs << std::endl;

    cuda_free(d_input);
    cuda_free(d_logits);
    model.deallocate();
}

/**
 * @brief Test forward pass with single token input
 */
TEST_F(GPTModelTest, ForwardSingleToken) {
    GPTModel model;
    model.config = gpt_tiny();
    model.allocate();

    int batch_size = 1;
    int seq_len = 1;
    int vocab_size = model.config.vocab_size;

    int h_input = 42;  // Arbitrary valid token
    int* d_input = cuda_malloc<int>(1);
    CHECK_CUDA(cudaMemcpy(d_input, &h_input, sizeof(int),
                         cudaMemcpyHostToDevice));

    float* d_logits = cuda_malloc<float>(vocab_size);

    model.forward(d_logits, d_input, batch_size, seq_len);
    CHECK_CUDA(cudaDeviceSynchronize());

    // Verify we get valid logits
    std::vector<float> h_logits(vocab_size);
    CHECK_CUDA(cudaMemcpy(h_logits.data(), d_logits,
                         vocab_size * sizeof(float),
                         cudaMemcpyDeviceToHost));

    int finite_count = 0;
    for (int i = 0; i < vocab_size; ++i) {
        if (std::isfinite(h_logits[i])) finite_count++;
    }
    EXPECT_EQ(finite_count, vocab_size);

    cuda_free(d_input);
    cuda_free(d_logits);
    model.deallocate();
}

/**
 * @brief Test that different inputs produce different outputs
 */
TEST_F(GPTModelTest, DifferentInputsDifferentOutputs) {
    GPTModel model;
    model.config = gpt_tiny();
    model.allocate();

    int seq_len = 4;
    int vocab_size = model.config.vocab_size;

    // Input 1: [0, 1, 2, 3]
    std::vector<int> h_input1 = {0, 1, 2, 3};
    // Input 2: [4, 5, 6, 7]
    std::vector<int> h_input2 = {4, 5, 6, 7};

    int* d_input1 = cuda_malloc<int>(seq_len);
    int* d_input2 = cuda_malloc<int>(seq_len);
    float* d_logits1 = cuda_malloc<float>((size_t)seq_len * vocab_size);
    float* d_logits2 = cuda_malloc<float>((size_t)seq_len * vocab_size);

    CHECK_CUDA(cudaMemcpy(d_input1, h_input1.data(), seq_len * sizeof(int),
                         cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_input2, h_input2.data(), seq_len * sizeof(int),
                         cudaMemcpyHostToDevice));

    model.forward(d_logits1, d_input1, 1, seq_len);
    model.forward(d_logits2, d_input2, 1, seq_len);
    CHECK_CUDA(cudaDeviceSynchronize());

    // Compare logits - they should differ
    size_t total = (size_t)seq_len * vocab_size;
    std::vector<float> h_logits1(total), h_logits2(total);
    CHECK_CUDA(cudaMemcpy(h_logits1.data(), d_logits1, total * sizeof(float),
                         cudaMemcpyDeviceToHost));
    CHECK_CUDA(cudaMemcpy(h_logits2.data(), d_logits2, total * sizeof(float),
                         cudaMemcpyDeviceToHost));

    float max_diff = 0.0f;
    for (size_t i = 0; i < total; ++i) {
        max_diff = std::max(max_diff, std::abs(h_logits1[i] - h_logits2[i]));
    }

    EXPECT_GT(max_diff, 0.0f) << "Different inputs produced identical outputs";
    std::cout << "Max logit difference between inputs: " << max_diff << std::endl;

    cuda_free(d_input1);
    cuda_free(d_input2);
    cuda_free(d_logits1);
    cuda_free(d_logits2);
    model.deallocate();
}
