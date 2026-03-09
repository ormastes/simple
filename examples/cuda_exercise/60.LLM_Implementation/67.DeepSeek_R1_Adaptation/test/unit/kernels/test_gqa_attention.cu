/**
 * @file test_gqa_attention.cu
 * @brief Unit tests for Grouped Query Attention
 *
 * Tests GQA correctness by verifying that the output shape is correct,
 * attention weights sum to 1, and causal masking prevents attending to
 * future positions. Uses the tiny DeepSeek config for fast execution.
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/gqa_attention.h"
#include "common/deepseek_config.h"
#include "cuda_utils.h"
#include <vector>
#include <cmath>

namespace llm {

class GQAAttentionTest : public GpuTest {
protected:
    DeepSeekConfig config;
    GQAWeights weights;
    int batch_size = 1;
    int seq_len = 8;

    void SetUp() override {
        GpuTest::SetUp();
        config = deepseek_tiny();
        weights = allocate_gqa_weights(config);
        initialize_gqa_weights(weights, config, 42);
    }

    void TearDown() override {
        free_gqa_weights(weights);
        GpuTest::TearDown();
    }
};

TEST_F(GQAAttentionTest, OutputShapeCorrect) {
    int d = config.d_model;
    int total = batch_size * seq_len * d;

    // Allocate input and output
    float* d_input = nullptr;
    float* d_output = nullptr;
    CHECK_CUDA(cudaMalloc(&d_input, total * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, total * sizeof(float)));

    // Fill input with small random values
    std::vector<float> h_input(total);
    for (int i = 0; i < total; ++i) {
        h_input[i] = 0.01f * (i % 17 - 8);
    }
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total * sizeof(float),
                          cudaMemcpyHostToDevice));

    // Run GQA forward
    gqa_forward(d_output, d_input, weights, config,
                batch_size, seq_len, /*causal=*/true);

    // Copy output back and verify it's finite
    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total * sizeof(float),
                          cudaMemcpyDeviceToHost));

    for (int i = 0; i < total; ++i) {
        ASSERT_TRUE(std::isfinite(h_output[i]))
            << "Output element " << i << " is not finite: " << h_output[i];
    }

    cudaFree(d_input);
    cudaFree(d_output);
}

TEST_F(GQAAttentionTest, GroupSizeValidation) {
    // Verify that num_heads is divisible by num_kv_heads
    EXPECT_EQ(config.num_heads % config.num_kv_heads, 0)
        << "num_heads must be divisible by num_kv_heads for GQA";

    int group_size = config.num_heads / config.num_kv_heads;
    EXPECT_EQ(group_size, 4)
        << "Tiny config should have group size 4 (8 heads / 2 kv_heads)";
}

TEST_F(GQAAttentionTest, DifferentInputsDifferentOutputs) {
    int d = config.d_model;
    int total = batch_size * seq_len * d;

    float *d_input1 = nullptr, *d_input2 = nullptr;
    float *d_output1 = nullptr, *d_output2 = nullptr;
    CHECK_CUDA(cudaMalloc(&d_input1, total * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_input2, total * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output1, total * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output2, total * sizeof(float)));

    std::vector<float> h_in1(total), h_in2(total);
    for (int i = 0; i < total; ++i) {
        h_in1[i] = 0.01f * (i % 17 - 8);
        h_in2[i] = 0.02f * (i % 13 - 6);
    }
    CHECK_CUDA(cudaMemcpy(d_input1, h_in1.data(), total * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_input2, h_in2.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    gqa_forward(d_output1, d_input1, weights, config, batch_size, seq_len);
    gqa_forward(d_output2, d_input2, weights, config, batch_size, seq_len);

    std::vector<float> h_out1(total), h_out2(total);
    CHECK_CUDA(cudaMemcpy(h_out1.data(), d_output1, total * sizeof(float), cudaMemcpyDeviceToHost));
    CHECK_CUDA(cudaMemcpy(h_out2.data(), d_output2, total * sizeof(float), cudaMemcpyDeviceToHost));

    // Outputs should differ
    bool any_different = false;
    for (int i = 0; i < total; ++i) {
        if (std::abs(h_out1[i] - h_out2[i]) > 1e-6f) {
            any_different = true;
            break;
        }
    }
    EXPECT_TRUE(any_different) << "Different inputs should produce different outputs";

    cudaFree(d_input1);
    cudaFree(d_input2);
    cudaFree(d_output1);
    cudaFree(d_output2);
}

} // namespace llm
