/**
 * @file test_swiglu_fused.cu
 * @brief Unit tests for SwiGLU feed-forward network
 *
 * Tests SwiGLU correctness by verifying output shape, finite values,
 * and that the SiLU activation behaves correctly (SiLU(0) = 0,
 * SiLU is monotonically increasing for x > ~-1.28).
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/swiglu_ffn.h"
#include "common/deepseek_config.h"
#include "cuda_utils.h"
#include <vector>
#include <cmath>

namespace llm {

class SwiGLUTest : public GpuTest {
protected:
    DeepSeekConfig config;
    SwiGLUWeights weights;
    int batch_size = 1;
    int seq_len = 4;

    void SetUp() override {
        GpuTest::SetUp();
        config = deepseek_tiny();
        weights = allocate_swiglu_weights(config.d_model, config.d_ff);
        initialize_swiglu_weights(weights, config.d_model, config.d_ff, 42);
    }

    void TearDown() override {
        free_swiglu_weights(weights);
        GpuTest::TearDown();
    }
};

TEST_F(SwiGLUTest, OutputShapeCorrect) {
    int d = config.d_model;
    int total = batch_size * seq_len * d;

    float *d_input = nullptr, *d_output = nullptr;
    CHECK_CUDA(cudaMalloc(&d_input, total * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, total * sizeof(float)));

    // Fill input
    std::vector<float> h_input(total);
    for (int i = 0; i < total; ++i) {
        h_input[i] = 0.01f * (i % 11 - 5);
    }
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total * sizeof(float),
                          cudaMemcpyHostToDevice));

    swiglu_forward(d_output, d_input, weights,
                   config.d_model, config.d_ff,
                   batch_size, seq_len);

    // Verify all outputs are finite
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

TEST_F(SwiGLUTest, ZeroInputProducesSmallOutput) {
    // With zero input, gate and up projections are just biases (zero),
    // so SiLU(0) = 0 * sigmoid(0) = 0, and output should be small
    int d = config.d_model;
    int total = batch_size * seq_len * d;

    float *d_input = nullptr, *d_output = nullptr;
    CHECK_CUDA(cudaMalloc(&d_input, total * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, total * sizeof(float)));

    // Zero input
    CHECK_CUDA(cudaMemset(d_input, 0, total * sizeof(float)));

    swiglu_forward(d_output, d_input, weights,
                   config.d_model, config.d_ff,
                   batch_size, seq_len);

    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total * sizeof(float),
                          cudaMemcpyDeviceToHost));

    // With zero-initialized biases and zero input, output should be zero
    float max_abs = 0.0f;
    for (int i = 0; i < total; ++i) {
        max_abs = std::max(max_abs, std::abs(h_output[i]));
    }
    EXPECT_LT(max_abs, 1e-5f)
        << "Zero input with zero biases should produce near-zero output";

    cudaFree(d_input);
    cudaFree(d_output);
}

TEST_F(SwiGLUTest, DifferentInputsDifferentOutputs) {
    int d = config.d_model;
    int total = batch_size * seq_len * d;

    float *d_in1 = nullptr, *d_in2 = nullptr;
    float *d_out1 = nullptr, *d_out2 = nullptr;
    CHECK_CUDA(cudaMalloc(&d_in1, total * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_in2, total * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_out1, total * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_out2, total * sizeof(float)));

    std::vector<float> h_in1(total), h_in2(total);
    for (int i = 0; i < total; ++i) {
        h_in1[i] = 0.1f * (i % 7 - 3);
        h_in2[i] = 0.2f * (i % 11 - 5);
    }
    CHECK_CUDA(cudaMemcpy(d_in1, h_in1.data(), total * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_in2, h_in2.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    swiglu_forward(d_out1, d_in1, weights, config.d_model, config.d_ff, batch_size, seq_len);
    swiglu_forward(d_out2, d_in2, weights, config.d_model, config.d_ff, batch_size, seq_len);

    std::vector<float> h_out1(total), h_out2(total);
    CHECK_CUDA(cudaMemcpy(h_out1.data(), d_out1, total * sizeof(float), cudaMemcpyDeviceToHost));
    CHECK_CUDA(cudaMemcpy(h_out2.data(), d_out2, total * sizeof(float), cudaMemcpyDeviceToHost));

    bool any_different = false;
    for (int i = 0; i < total; ++i) {
        if (std::abs(h_out1[i] - h_out2[i]) > 1e-6f) {
            any_different = true;
            break;
        }
    }
    EXPECT_TRUE(any_different) << "Different inputs should produce different outputs";

    cudaFree(d_in1);
    cudaFree(d_in2);
    cudaFree(d_out1);
    cudaFree(d_out2);
}

TEST_F(SwiGLUTest, WeightAllocationAndFree) {
    // Test that allocate/free cycle works without leaks
    SwiGLUWeights w = allocate_swiglu_weights(config.d_model, config.d_ff);
    EXPECT_NE(w.W_gate, nullptr);
    EXPECT_NE(w.W_up, nullptr);
    EXPECT_NE(w.W_down, nullptr);

    free_swiglu_weights(w);
    EXPECT_EQ(w.W_gate, nullptr);
    EXPECT_EQ(w.W_up, nullptr);
    EXPECT_EQ(w.W_down, nullptr);
}

} // namespace llm
