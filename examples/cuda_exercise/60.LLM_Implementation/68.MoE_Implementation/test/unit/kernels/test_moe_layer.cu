/**
 * @file test_moe_layer.cu
 * @brief Unit tests for the complete MoE layer forward pass
 *
 * Tests the end-to-end MoE layer by verifying:
 * - Output has the correct shape and finite values
 * - Different inputs produce different outputs
 * - Auxiliary load balancing loss is computed
 * - MoE transformer config correctly identifies MoE layers
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/moe_layer.h"
#include "common/moe_transformer.h"
#include "cuda_utils.h"
#include <vector>
#include <cmath>
#include <random>

namespace llm {

class MoELayerTest : public GpuTest {
protected:
    MoELayerConfig config;
    ExpertWeights experts;
    float* d_W_router = nullptr;
    int num_tokens = 8;

    void SetUp() override {
        GpuTest::SetUp();
        config = MoELayerConfig(/*num_experts=*/4, /*top_k=*/2,
                               /*d_model=*/32, /*d_ff=*/64,
                               /*aux_loss_weight=*/0.01f);

        experts = allocate_expert_weights(config.router.num_experts,
                                          config.d_model, config.d_ff);
        initialize_expert_weights(experts, 42);

        // Allocate and initialize router gate weights
        int gate_size = config.router.num_experts * config.d_model;
        CHECK_CUDA(cudaMalloc(&d_W_router, gate_size * sizeof(float)));

        std::vector<float> h_gate(gate_size);
        std::default_random_engine gen(123);
        float stddev = 1.0f / std::sqrt(static_cast<float>(config.d_model));
        std::normal_distribution<float> dist(0.0f, stddev);
        for (auto& v : h_gate) v = dist(gen);
        CHECK_CUDA(cudaMemcpy(d_W_router, h_gate.data(), gate_size * sizeof(float),
                              cudaMemcpyHostToDevice));
    }

    void TearDown() override {
        free_expert_weights(experts);
        if (d_W_router) cudaFree(d_W_router);
        GpuTest::TearDown();
    }
};

TEST_F(MoELayerTest, ForwardProducesFiniteOutput) {
    int total = num_tokens * config.d_model;

    float* d_input = nullptr;
    float* d_output = nullptr;
    CHECK_CUDA(cudaMalloc(&d_input, total * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, total * sizeof(float)));

    // Fill input
    std::vector<float> h_input(total);
    for (int i = 0; i < total; i++) {
        h_input[i] = 0.01f * (i % 13 - 6);
    }
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total * sizeof(float),
                          cudaMemcpyHostToDevice));

    // Run MoE layer forward
    moe_layer_forward(d_output, d_input, d_W_router, experts,
                     config, num_tokens, nullptr);

    // Verify output is finite
    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total * sizeof(float),
                          cudaMemcpyDeviceToHost));

    for (int i = 0; i < total; i++) {
        ASSERT_TRUE(std::isfinite(h_output[i]))
            << "MoE output element " << i << " is not finite: " << h_output[i];
    }

    cudaFree(d_input);
    cudaFree(d_output);
}

TEST_F(MoELayerTest, DifferentInputsDifferentOutputs) {
    int total = num_tokens * config.d_model;

    float *d_in1 = nullptr, *d_in2 = nullptr;
    float *d_out1 = nullptr, *d_out2 = nullptr;
    CHECK_CUDA(cudaMalloc(&d_in1, total * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_in2, total * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_out1, total * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_out2, total * sizeof(float)));

    std::vector<float> h_in1(total), h_in2(total);
    for (int i = 0; i < total; i++) {
        h_in1[i] = 0.01f * (i % 11 - 5);
        h_in2[i] = 0.02f * (i % 7 - 3);
    }
    CHECK_CUDA(cudaMemcpy(d_in1, h_in1.data(), total * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_in2, h_in2.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    moe_layer_forward(d_out1, d_in1, d_W_router, experts, config, num_tokens);
    moe_layer_forward(d_out2, d_in2, d_W_router, experts, config, num_tokens);

    std::vector<float> h_out1(total), h_out2(total);
    CHECK_CUDA(cudaMemcpy(h_out1.data(), d_out1, total * sizeof(float), cudaMemcpyDeviceToHost));
    CHECK_CUDA(cudaMemcpy(h_out2.data(), d_out2, total * sizeof(float), cudaMemcpyDeviceToHost));

    bool any_diff = false;
    for (int i = 0; i < total; i++) {
        if (std::abs(h_out1[i] - h_out2[i]) > 1e-6f) {
            any_diff = true;
            break;
        }
    }
    EXPECT_TRUE(any_diff) << "Different inputs should produce different MoE outputs";

    cudaFree(d_in1);
    cudaFree(d_in2);
    cudaFree(d_out1);
    cudaFree(d_out2);
}

TEST_F(MoELayerTest, AuxLossIsComputed) {
    int total = num_tokens * config.d_model;

    float* d_input = nullptr;
    float* d_output = nullptr;
    float* d_loss = nullptr;
    CHECK_CUDA(cudaMalloc(&d_input, total * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, total * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_loss, sizeof(float)));

    std::vector<float> h_input(total, 0.01f);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total * sizeof(float),
                          cudaMemcpyHostToDevice));

    moe_layer_forward(d_output, d_input, d_W_router, experts,
                     config, num_tokens, d_loss);

    float h_loss = 0.0f;
    CHECK_CUDA(cudaMemcpy(&h_loss, d_loss, sizeof(float), cudaMemcpyDeviceToHost));

    EXPECT_TRUE(std::isfinite(h_loss)) << "Auxiliary loss should be finite";
    EXPECT_GE(h_loss, 0.0f) << "Auxiliary loss should be non-negative";

    cudaFree(d_input);
    cudaFree(d_output);
    cudaFree(d_loss);
}

TEST_F(MoELayerTest, TransformerConfigIdentifiesMoELayers) {
    DeepSeekConfig base = deepseek_tiny();
    base.num_experts = 4;
    base.top_k_experts = 2;

    MoETransformerConfig moe_config(base, /*first_moe_layer=*/2);

    EXPECT_FALSE(is_moe_layer(0, moe_config)) << "Layer 0 should be dense";
    EXPECT_FALSE(is_moe_layer(1, moe_config)) << "Layer 1 should be dense";
    EXPECT_TRUE(is_moe_layer(2, moe_config)) << "Layer 2 should be MoE";
    EXPECT_TRUE(is_moe_layer(5, moe_config)) << "Layer 5 should be MoE";
}

TEST_F(MoELayerTest, DenseConfigHasNoMoELayers) {
    DeepSeekConfig base = deepseek_tiny();
    base.num_experts = 0;  // Dense model

    MoETransformerConfig moe_config(base, /*first_moe_layer=*/0);

    for (int l = 0; l < base.num_layers; l++) {
        EXPECT_FALSE(is_moe_layer(l, moe_config))
            << "Layer " << l << " should be dense when num_experts=0";
    }
}

} // namespace llm
