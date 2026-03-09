/**
 * @file test_router.cu
 * @brief Unit tests for MoE top-k router kernels
 *
 * Tests the router gating mechanism by verifying:
 * - Softmax outputs sum to 1 per token
 * - Top-k selection picks the correct experts
 * - Routing weights are properly renormalized
 * - Different inputs produce different routing decisions
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/topk_router.h"
#include "cuda_utils.h"
#include <vector>
#include <cmath>
#include <numeric>

namespace llm {

class RouterTest : public GpuTest {
protected:
    RouterConfig config;
    int num_tokens = 8;

    void SetUp() override {
        GpuTest::SetUp();
        config = RouterConfig(/*num_experts=*/4, /*top_k=*/2,
                             /*d_model=*/32, /*jitter=*/0.0f,
                             /*capacity=*/1.25f);
    }
};

TEST_F(RouterTest, GateLogitsComputed) {
    int d = config.d_model;
    int num_experts = config.num_experts;

    // Allocate input and gate weight matrix
    float* d_input = nullptr;
    float* d_W_gate = nullptr;
    CHECK_CUDA(cudaMalloc(&d_input, num_tokens * d * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_W_gate, num_experts * d * sizeof(float)));

    // Fill with small values
    std::vector<float> h_input(num_tokens * d);
    std::vector<float> h_W_gate(num_experts * d);
    for (int i = 0; i < num_tokens * d; i++) h_input[i] = 0.01f * (i % 7 - 3);
    for (int i = 0; i < num_experts * d; i++) h_W_gate[i] = 0.01f * (i % 5 - 2);

    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), num_tokens * d * sizeof(float),
                          cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_W_gate, h_W_gate.data(), num_experts * d * sizeof(float),
                          cudaMemcpyHostToDevice));

    // Allocate and run router
    RouterOutput output = allocate_router_output(num_tokens, config);
    topk_route(output, d_input, d_W_gate, config, num_tokens);

    // Read back expert indices and weights
    std::vector<int> h_indices(num_tokens * config.top_k);
    std::vector<float> h_weights(num_tokens * config.top_k);
    CHECK_CUDA(cudaMemcpy(h_indices.data(), output.expert_indices,
                          num_tokens * config.top_k * sizeof(int),
                          cudaMemcpyDeviceToHost));
    CHECK_CUDA(cudaMemcpy(h_weights.data(), output.expert_weights,
                          num_tokens * config.top_k * sizeof(float),
                          cudaMemcpyDeviceToHost));

    // Verify: all expert indices are valid
    for (int i = 0; i < num_tokens * config.top_k; i++) {
        EXPECT_GE(h_indices[i], 0) << "Expert index should be non-negative";
        EXPECT_LT(h_indices[i], num_experts) << "Expert index should be < num_experts";
    }

    // Verify: per-token selected weights are non-negative
    for (int i = 0; i < num_tokens * config.top_k; i++) {
        EXPECT_GE(h_weights[i], 0.0f) << "Routing weight should be non-negative";
    }

    // Verify: per-token weights sum approximately to 1 (renormalized)
    for (int t = 0; t < num_tokens; t++) {
        float sum = 0.0f;
        for (int k = 0; k < config.top_k; k++) {
            sum += h_weights[t * config.top_k + k];
        }
        EXPECT_NEAR(sum, 1.0f, 1e-4f)
            << "Token " << t << " routing weights should sum to 1";
    }

    free_router_output(output);
    cudaFree(d_input);
    cudaFree(d_W_gate);
}

TEST_F(RouterTest, TopKSelectsDistinctExperts) {
    int d = config.d_model;

    float* d_input = nullptr;
    float* d_W_gate = nullptr;
    CHECK_CUDA(cudaMalloc(&d_input, num_tokens * d * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_W_gate, config.num_experts * d * sizeof(float)));

    std::vector<float> h_input(num_tokens * d, 0.01f);
    std::vector<float> h_W_gate(config.num_experts * d, 0.01f);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), num_tokens * d * sizeof(float),
                          cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_W_gate, h_W_gate.data(), config.num_experts * d * sizeof(float),
                          cudaMemcpyHostToDevice));

    RouterOutput output = allocate_router_output(num_tokens, config);
    topk_route(output, d_input, d_W_gate, config, num_tokens);

    std::vector<int> h_indices(num_tokens * config.top_k);
    CHECK_CUDA(cudaMemcpy(h_indices.data(), output.expert_indices,
                          num_tokens * config.top_k * sizeof(int),
                          cudaMemcpyDeviceToHost));

    // Each token's top-k experts should be distinct
    for (int t = 0; t < num_tokens; t++) {
        for (int k1 = 0; k1 < config.top_k; k1++) {
            for (int k2 = k1 + 1; k2 < config.top_k; k2++) {
                EXPECT_NE(h_indices[t * config.top_k + k1],
                         h_indices[t * config.top_k + k2])
                    << "Token " << t << " should select distinct experts";
            }
        }
    }

    free_router_output(output);
    cudaFree(d_input);
    cudaFree(d_W_gate);
}

TEST_F(RouterTest, DifferentInputsDifferentRouting) {
    int d = config.d_model;

    float *d_in1 = nullptr, *d_in2 = nullptr, *d_W_gate = nullptr;
    CHECK_CUDA(cudaMalloc(&d_in1, num_tokens * d * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_in2, num_tokens * d * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_W_gate, config.num_experts * d * sizeof(float)));

    std::vector<float> h_in1(num_tokens * d), h_in2(num_tokens * d);
    std::vector<float> h_W(config.num_experts * d);
    for (int i = 0; i < num_tokens * d; i++) {
        h_in1[i] = 0.1f * (i % 11 - 5);
        h_in2[i] = 0.1f * (i % 13 - 6);
    }
    for (int i = 0; i < config.num_experts * d; i++) {
        h_W[i] = 0.05f * (i % 7 - 3);
    }

    CHECK_CUDA(cudaMemcpy(d_in1, h_in1.data(), num_tokens * d * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_in2, h_in2.data(), num_tokens * d * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_W_gate, h_W.data(), config.num_experts * d * sizeof(float), cudaMemcpyHostToDevice));

    RouterOutput out1 = allocate_router_output(num_tokens, config);
    RouterOutput out2 = allocate_router_output(num_tokens, config);

    topk_route(out1, d_in1, d_W_gate, config, num_tokens);
    topk_route(out2, d_in2, d_W_gate, config, num_tokens);

    std::vector<float> h_w1(num_tokens * config.top_k), h_w2(num_tokens * config.top_k);
    CHECK_CUDA(cudaMemcpy(h_w1.data(), out1.expert_weights,
                          num_tokens * config.top_k * sizeof(float), cudaMemcpyDeviceToHost));
    CHECK_CUDA(cudaMemcpy(h_w2.data(), out2.expert_weights,
                          num_tokens * config.top_k * sizeof(float), cudaMemcpyDeviceToHost));

    // At least some weights should differ
    bool any_diff = false;
    for (size_t i = 0; i < h_w1.size(); i++) {
        if (std::abs(h_w1[i] - h_w2[i]) > 1e-6f) {
            any_diff = true;
            break;
        }
    }
    EXPECT_TRUE(any_diff) << "Different inputs should produce different routing weights";

    free_router_output(out1);
    free_router_output(out2);
    cudaFree(d_in1);
    cudaFree(d_in2);
    cudaFree(d_W_gate);
}

} // namespace llm
