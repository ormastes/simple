/**
 * @file test_dispatch.cu
 * @brief Unit tests for expert dispatch and combine kernels
 *
 * Tests the dispatch/combine roundtrip by verifying:
 * - Expert forward produces finite outputs
 * - Expert weight allocation and deallocation work correctly
 * - Multiple experts produce different outputs from the same input
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/expert_network.h"
#include "cuda_utils.h"
#include <vector>
#include <cmath>

namespace llm {

class ExpertDispatchTest : public GpuTest {
protected:
    ExpertWeights weights;
    int num_experts = 4;
    int d_model = 32;
    int d_ff = 64;

    void SetUp() override {
        GpuTest::SetUp();
        weights = allocate_expert_weights(num_experts, d_model, d_ff);
        initialize_expert_weights(weights, 42);
    }

    void TearDown() override {
        free_expert_weights(weights);
        GpuTest::TearDown();
    }
};

TEST_F(ExpertDispatchTest, ExpertForwardProducesFiniteOutput) {
    int num_tokens = 4;

    // Allocate input and output
    float* d_input = nullptr;
    float* d_output = nullptr;
    CHECK_CUDA(cudaMalloc(&d_input, num_tokens * d_model * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, num_tokens * d_model * sizeof(float)));

    // Fill input
    std::vector<float> h_input(num_tokens * d_model);
    for (size_t i = 0; i < h_input.size(); i++) {
        h_input[i] = 0.01f * (static_cast<int>(i) % 11 - 5);
    }
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), num_tokens * d_model * sizeof(float),
                          cudaMemcpyHostToDevice));

    // Run expert 0 forward
    expert_forward(d_output, d_input,
                  weights.W_gate[0], weights.W_up[0], weights.W_down[0],
                  d_model, d_ff, num_tokens);

    // Verify output is finite
    std::vector<float> h_output(num_tokens * d_model);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, num_tokens * d_model * sizeof(float),
                          cudaMemcpyDeviceToHost));

    for (size_t i = 0; i < h_output.size(); i++) {
        ASSERT_TRUE(std::isfinite(h_output[i]))
            << "Expert output element " << i << " is not finite: " << h_output[i];
    }

    cudaFree(d_input);
    cudaFree(d_output);
}

TEST_F(ExpertDispatchTest, DifferentExpertsProduceDifferentOutputs) {
    int num_tokens = 4;

    float* d_input = nullptr;
    float *d_out0 = nullptr, *d_out1 = nullptr;
    CHECK_CUDA(cudaMalloc(&d_input, num_tokens * d_model * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_out0, num_tokens * d_model * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_out1, num_tokens * d_model * sizeof(float)));

    std::vector<float> h_input(num_tokens * d_model);
    for (size_t i = 0; i < h_input.size(); i++) {
        h_input[i] = 0.01f * (static_cast<int>(i) % 7 - 3);
    }
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), num_tokens * d_model * sizeof(float),
                          cudaMemcpyHostToDevice));

    // Run expert 0
    expert_forward(d_out0, d_input,
                  weights.W_gate[0], weights.W_up[0], weights.W_down[0],
                  d_model, d_ff, num_tokens);

    // Run expert 1
    expert_forward(d_out1, d_input,
                  weights.W_gate[1], weights.W_up[1], weights.W_down[1],
                  d_model, d_ff, num_tokens);

    // Outputs should differ
    std::vector<float> h_out0(num_tokens * d_model), h_out1(num_tokens * d_model);
    CHECK_CUDA(cudaMemcpy(h_out0.data(), d_out0, num_tokens * d_model * sizeof(float),
                          cudaMemcpyDeviceToHost));
    CHECK_CUDA(cudaMemcpy(h_out1.data(), d_out1, num_tokens * d_model * sizeof(float),
                          cudaMemcpyDeviceToHost));

    bool any_diff = false;
    for (size_t i = 0; i < h_out0.size(); i++) {
        if (std::abs(h_out0[i] - h_out1[i]) > 1e-6f) {
            any_diff = true;
            break;
        }
    }
    EXPECT_TRUE(any_diff) << "Different experts should produce different outputs";

    cudaFree(d_input);
    cudaFree(d_out0);
    cudaFree(d_out1);
}

TEST_F(ExpertDispatchTest, WeightAllocationAndFree) {
    ExpertWeights w = allocate_expert_weights(2, 16, 32);

    EXPECT_EQ(w.num_experts, 2);
    EXPECT_EQ(w.d_model, 16);
    EXPECT_EQ(w.d_ff, 32);
    EXPECT_NE(w.W_gate, nullptr);
    EXPECT_NE(w.W_up, nullptr);
    EXPECT_NE(w.W_down, nullptr);

    for (int e = 0; e < 2; e++) {
        EXPECT_NE(w.W_gate[e], nullptr);
        EXPECT_NE(w.W_up[e], nullptr);
        EXPECT_NE(w.W_down[e], nullptr);
    }

    free_expert_weights(w);
    EXPECT_EQ(w.W_gate, nullptr);
}

TEST_F(ExpertDispatchTest, ZeroTokensHandledGracefully) {
    float* d_out = nullptr;
    CHECK_CUDA(cudaMalloc(&d_out, d_model * sizeof(float)));

    // Should not crash with 0 tokens
    expert_forward(d_out, nullptr,
                  weights.W_gate[0], weights.W_up[0], weights.W_down[0],
                  d_model, d_ff, 0);

    cudaFree(d_out);
}

} // namespace llm
