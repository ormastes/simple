/**
 * @file test_cpu_experts.cu
 * @brief Unit tests for CPU Mixture of Experts implementation
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cpu_experts.h"
#include <vector>
#include <random>
#include <cmath>
#include <numeric>
#include <algorithm>
#include <iostream>

/**
 * @brief Test fixture for CPU MoE tests
 *
 * Provides helpers for generating random data, computing reference
 * GELU/FFN/MoE, and comparing results with tolerance.
 */
class CPUExpertsTest : public ::testing::Test {
protected:
    void SetUp() override {
        gen.seed(12345);
    }

    std::mt19937 gen;

    /// Generate random float vector with uniform distribution [-scale, scale]
    std::vector<float> randomVector(int size, float scale = 1.0f) {
        std::vector<float> vec(size);
        std::uniform_real_distribution<float> dist(-scale, scale);
        for (auto& val : vec) {
            val = dist(gen);
        }
        return vec;
    }

    /// Reference GELU: x * 0.5 * (1 + tanh(sqrt(2/pi) * (x + 0.044715 * x^3)))
    float referenceGelu(float x) {
        float x3 = x * x * x;
        float inner = 0.7978845608f * (x + 0.044715f * x3);
        return 0.5f * x * (1.0f + tanhf(inner));
    }

    /// Reference single expert FFN
    std::vector<float> referenceExpertFFN(const float* input,
                                          const float* W1, const float* b1,
                                          const float* W2, const float* b2,
                                          int batch_size, int d_model, int d_ff) {
        std::vector<float> hidden(batch_size * d_ff);
        std::vector<float> output(batch_size * d_model);

        // First layer + GELU
        for (int b = 0; b < batch_size; b++) {
            for (int f = 0; f < d_ff; f++) {
                float sum = b1[f];
                for (int d = 0; d < d_model; d++) {
                    sum += input[b * d_model + d] * W1[f * d_model + d];
                }
                hidden[b * d_ff + f] = referenceGelu(sum);
            }
        }

        // Second layer
        for (int b = 0; b < batch_size; b++) {
            for (int d = 0; d < d_model; d++) {
                float sum = b2[d];
                for (int f = 0; f < d_ff; f++) {
                    sum += hidden[b * d_ff + f] * W2[d * d_ff + f];
                }
                output[b * d_model + d] = sum;
            }
        }

        return output;
    }

    /// Compare two float arrays with tolerance
    bool arraysEqual(const float* A, const float* B, int size, float tol = 1e-4f) {
        for (int i = 0; i < size; i++) {
            if (std::abs(A[i] - B[i]) > tol) {
                return false;
            }
        }
        return true;
    }

    /// Compute max absolute difference
    float maxAbsDiff(const float* A, const float* B, int size) {
        float max_diff = 0.0f;
        for (int i = 0; i < size; i++) {
            float diff = std::abs(A[i] - B[i]);
            if (diff > max_diff) max_diff = diff;
        }
        return max_diff;
    }
};

// ============================================================
// GELU Correctness Tests
// ============================================================

/**
 * @brief Test GELU activation at known values
 */
TEST_F(CPUExpertsTest, GELUCorrectness) {
    std::vector<float> input = {-2.0f, -1.0f, -0.5f, 0.0f, 0.5f, 1.0f, 2.0f};
    std::vector<float> output(input.size());

    cpu_gelu(output.data(), input.data(), static_cast<int>(input.size()));

    for (size_t i = 0; i < input.size(); i++) {
        float expected = referenceGelu(input[i]);
        EXPECT_NEAR(output[i], expected, 1e-6f)
            << "GELU mismatch at index " << i << " input=" << input[i];
    }
}

/**
 * @brief Test GELU with zero input
 */
TEST_F(CPUExpertsTest, GELUZero) {
    float input = 0.0f;
    float output = -1.0f;
    cpu_gelu(&output, &input, 1);
    EXPECT_NEAR(output, 0.0f, 1e-7f);
}

/**
 * @brief Test GELU with random values
 */
TEST_F(CPUExpertsTest, GELURandomValues) {
    const int n = 1024;
    auto input = randomVector(n, 3.0f);
    std::vector<float> output(n);

    cpu_gelu(output.data(), input.data(), n);

    for (int i = 0; i < n; i++) {
        float expected = referenceGelu(input[i]);
        EXPECT_NEAR(output[i], expected, 1e-5f)
            << "GELU mismatch at index " << i;
    }
}

// ============================================================
// Top-K Gating Tests
// ============================================================

/**
 * @brief Test top-k gating correctness with clear logit separation
 */
TEST_F(CPUExpertsTest, TopKGatingCorrectness) {
    const int batch_size = 4;
    const int num_experts = 8;
    const int top_k = 2;

    // Create gate logits with clear top experts
    std::vector<float> gate_logits(batch_size * num_experts, 0.0f);

    // Token 0: experts 2 and 5 should be selected
    gate_logits[0 * num_experts + 2] = 10.0f;
    gate_logits[0 * num_experts + 5] = 8.0f;

    // Token 1: experts 0 and 7 should be selected
    gate_logits[1 * num_experts + 0] = 12.0f;
    gate_logits[1 * num_experts + 7] = 9.0f;

    // Token 2: experts 3 and 1 should be selected
    gate_logits[2 * num_experts + 3] = 15.0f;
    gate_logits[2 * num_experts + 1] = 7.0f;

    // Token 3: experts 6 and 4 should be selected
    gate_logits[3 * num_experts + 6] = 11.0f;
    gate_logits[3 * num_experts + 4] = 6.0f;

    std::vector<int> expert_indices(batch_size * top_k);
    std::vector<float> expert_weights(batch_size * top_k);

    cpu_topk_gating(expert_indices.data(), expert_weights.data(),
                    gate_logits.data(), batch_size, num_experts, top_k);

    // Verify token 0: top experts should be 2 and 5 (in order)
    EXPECT_EQ(expert_indices[0 * top_k + 0], 2);
    EXPECT_EQ(expert_indices[0 * top_k + 1], 5);

    // Verify token 1: top experts should be 0 and 7
    EXPECT_EQ(expert_indices[1 * top_k + 0], 0);
    EXPECT_EQ(expert_indices[1 * top_k + 1], 7);

    // Verify weights sum to 1 for each token
    for (int b = 0; b < batch_size; b++) {
        float weight_sum = 0.0f;
        for (int k = 0; k < top_k; k++) {
            weight_sum += expert_weights[b * top_k + k];
            EXPECT_GT(expert_weights[b * top_k + k], 0.0f)
                << "Weight should be positive for token " << b;
        }
        EXPECT_NEAR(weight_sum, 1.0f, 1e-5f)
            << "Weights should sum to 1 for token " << b;
    }
}

/**
 * @brief Test top-k=1 selects the single best expert
 */
TEST_F(CPUExpertsTest, TopKGatingK1) {
    const int batch_size = 2;
    const int num_experts = 4;
    const int top_k = 1;

    std::vector<float> gate_logits = {
        1.0f, 5.0f, 3.0f, 2.0f,   // Token 0: expert 1 wins
        0.0f, 0.0f, 10.0f, 0.0f   // Token 1: expert 2 wins
    };

    std::vector<int> expert_indices(batch_size * top_k);
    std::vector<float> expert_weights(batch_size * top_k);

    cpu_topk_gating(expert_indices.data(), expert_weights.data(),
                    gate_logits.data(), batch_size, num_experts, top_k);

    EXPECT_EQ(expert_indices[0], 1);
    EXPECT_EQ(expert_indices[1], 2);

    // With top_k=1, weight should be 1.0
    EXPECT_NEAR(expert_weights[0], 1.0f, 1e-5f);
    EXPECT_NEAR(expert_weights[1], 1.0f, 1e-5f);
}

// ============================================================
// Expert FFN Tests
// ============================================================

/**
 * @brief Test single expert FFN correctness
 */
TEST_F(CPUExpertsTest, ExpertFFNCorrectness) {
    const int batch_size = 4;
    const int d_model = 16;
    const int d_ff = 32;
    const int num_experts = 4;
    const int expert_idx = 1;

    auto input = randomVector(batch_size * d_model, 0.1f);

    // Create flat weight buffers for all experts
    auto W1 = randomVector(num_experts * d_ff * d_model, 0.1f);
    auto b1 = randomVector(num_experts * d_ff, 0.1f);
    auto W2 = randomVector(num_experts * d_model * d_ff, 0.1f);
    auto b2 = randomVector(num_experts * d_model, 0.1f);

    std::vector<float> output(batch_size * d_model);

    cpu_expert_ffn(output.data(), input.data(),
                  W1.data(), b1.data(), W2.data(), b2.data(),
                  batch_size, d_model, d_ff, expert_idx, num_experts);

    // Compute reference using this expert's weights
    const float* W1_e = &W1[expert_idx * d_ff * d_model];
    const float* b1_e = &b1[expert_idx * d_ff];
    const float* W2_e = &W2[expert_idx * d_model * d_ff];
    const float* b2_e = &b2[expert_idx * d_model];

    auto ref = referenceExpertFFN(input.data(), W1_e, b1_e, W2_e, b2_e,
                                   batch_size, d_model, d_ff);

    float max_diff = maxAbsDiff(output.data(), ref.data(), batch_size * d_model);
    EXPECT_LT(max_diff, 1e-4f) << "Expert FFN max diff: " << max_diff;
}

/**
 * @brief Test expert FFN with different expert indices
 */
TEST_F(CPUExpertsTest, ExpertFFNDifferentExperts) {
    const int batch_size = 2;
    const int d_model = 8;
    const int d_ff = 16;
    const int num_experts = 4;

    auto input = randomVector(batch_size * d_model, 0.1f);
    auto W1 = randomVector(num_experts * d_ff * d_model, 0.1f);
    auto b1 = randomVector(num_experts * d_ff, 0.1f);
    auto W2 = randomVector(num_experts * d_model * d_ff, 0.1f);
    auto b2 = randomVector(num_experts * d_model, 0.1f);

    // Different experts should produce different outputs
    std::vector<float> output0(batch_size * d_model);
    std::vector<float> output1(batch_size * d_model);

    cpu_expert_ffn(output0.data(), input.data(),
                  W1.data(), b1.data(), W2.data(), b2.data(),
                  batch_size, d_model, d_ff, 0, num_experts);

    cpu_expert_ffn(output1.data(), input.data(),
                  W1.data(), b1.data(), W2.data(), b2.data(),
                  batch_size, d_model, d_ff, 1, num_experts);

    // Outputs should differ since experts have different weights
    bool outputs_differ = false;
    for (int i = 0; i < batch_size * d_model; i++) {
        if (std::abs(output0[i] - output1[i]) > 1e-6f) {
            outputs_differ = true;
            break;
        }
    }
    EXPECT_TRUE(outputs_differ) << "Different experts should produce different outputs";
}

// ============================================================
// Full MoE Forward Tests
// ============================================================

/**
 * @brief Test complete MoE forward pass correctness
 */
TEST_F(CPUExpertsTest, MoEForwardCorrectness) {
    const int batch_size = 8;
    const int d_model = 16;
    const int d_ff = 32;
    const int num_experts = 4;
    const int top_k = 2;

    auto input = randomVector(batch_size * d_model, 0.1f);
    auto gate_weights = randomVector(num_experts * d_model, 0.1f);
    auto W1 = randomVector(num_experts * d_ff * d_model, 0.1f);
    auto b1 = randomVector(num_experts * d_ff, 0.1f);
    auto W2 = randomVector(num_experts * d_model * d_ff, 0.1f);
    auto b2 = randomVector(num_experts * d_model, 0.1f);

    std::vector<float> output(batch_size * d_model);

    cpu_moe_forward(output.data(), input.data(), gate_weights.data(),
                   W1.data(), b1.data(), W2.data(), b2.data(),
                   batch_size, d_model, d_ff, num_experts, top_k);

    // Manually compute reference:
    // 1. Gate logits
    std::vector<float> gate_logits(batch_size * num_experts);
    for (int b = 0; b < batch_size; b++) {
        for (int e = 0; e < num_experts; e++) {
            float sum = 0.0f;
            for (int d = 0; d < d_model; d++) {
                sum += input[b * d_model + d] * gate_weights[e * d_model + d];
            }
            gate_logits[b * num_experts + e] = sum;
        }
    }

    // 2. Top-k gating
    std::vector<int> expert_indices(batch_size * top_k);
    std::vector<float> expert_wts(batch_size * top_k);
    cpu_topk_gating(expert_indices.data(), expert_wts.data(),
                    gate_logits.data(), batch_size, num_experts, top_k);

    // 3. Compute weighted expert outputs
    std::vector<float> ref_output(batch_size * d_model, 0.0f);
    std::vector<float> expert_out(d_model);

    for (int b = 0; b < batch_size; b++) {
        for (int k = 0; k < top_k; k++) {
            int eidx = expert_indices[b * top_k + k];
            float weight = expert_wts[b * top_k + k];

            cpu_expert_ffn(expert_out.data(), &input[b * d_model],
                          W1.data(), b1.data(), W2.data(), b2.data(),
                          1, d_model, d_ff, eidx, num_experts);

            for (int d = 0; d < d_model; d++) {
                ref_output[b * d_model + d] += weight * expert_out[d];
            }
        }
    }

    float max_diff = maxAbsDiff(output.data(), ref_output.data(), batch_size * d_model);
    EXPECT_LT(max_diff, 1e-4f) << "MoE forward max diff: " << max_diff;
}

/**
 * @brief Test MoE forward with top_k=1 (single expert per token)
 */
TEST_F(CPUExpertsTest, MoEForwardTopK1) {
    const int batch_size = 4;
    const int d_model = 8;
    const int d_ff = 16;
    const int num_experts = 4;
    const int top_k = 1;

    auto input = randomVector(batch_size * d_model, 0.1f);
    auto gate_weights = randomVector(num_experts * d_model, 0.1f);
    auto W1 = randomVector(num_experts * d_ff * d_model, 0.1f);
    auto b1 = randomVector(num_experts * d_ff, 0.1f);
    auto W2 = randomVector(num_experts * d_model * d_ff, 0.1f);
    auto b2 = randomVector(num_experts * d_model, 0.1f);

    std::vector<float> output(batch_size * d_model);

    cpu_moe_forward(output.data(), input.data(), gate_weights.data(),
                   W1.data(), b1.data(), W2.data(), b2.data(),
                   batch_size, d_model, d_ff, num_experts, top_k);

    // Output should be non-zero (sanity check)
    bool has_nonzero = false;
    for (int i = 0; i < batch_size * d_model; i++) {
        if (std::abs(output[i]) > 1e-8f) {
            has_nonzero = true;
            break;
        }
    }
    EXPECT_TRUE(has_nonzero) << "MoE output should be non-zero";
}

// ============================================================
// Parallel Correctness Tests
// ============================================================

/**
 * @brief Test parallel MoE matches naive implementation
 */
TEST_F(CPUExpertsTest, ParallelCorrectness) {
    const int batch_size = 16;
    const int d_model = 32;
    const int d_ff = 64;
    const int num_experts = 8;
    const int top_k = 2;

    auto input = randomVector(batch_size * d_model, 0.1f);
    auto gate_weights = randomVector(num_experts * d_model, 0.1f);
    auto W1 = randomVector(num_experts * d_ff * d_model, 0.1f);
    auto b1 = randomVector(num_experts * d_ff, 0.1f);
    auto W2 = randomVector(num_experts * d_model * d_ff, 0.1f);
    auto b2 = randomVector(num_experts * d_model, 0.1f);

    std::vector<float> output_naive(batch_size * d_model);
    std::vector<float> output_parallel(batch_size * d_model);

    cpu_moe_forward(output_naive.data(), input.data(), gate_weights.data(),
                   W1.data(), b1.data(), W2.data(), b2.data(),
                   batch_size, d_model, d_ff, num_experts, top_k);

    cpu_moe_forward_parallel(output_parallel.data(), input.data(), gate_weights.data(),
                            W1.data(), b1.data(), W2.data(), b2.data(),
                            batch_size, d_model, d_ff, num_experts, top_k, 4);

    float max_diff = maxAbsDiff(output_naive.data(), output_parallel.data(),
                                 batch_size * d_model);
    EXPECT_LT(max_diff, 1e-4f)
        << "Parallel should match naive, max diff: " << max_diff;
}

// ============================================================
// Parameterized Tests
// ============================================================

/**
 * @brief Parameterized test for various MoE configurations
 *
 * Parameters: (batch_size, d_model, num_experts, top_k)
 */
class MoEConfigTest : public CPUExpertsTest,
                      public ::testing::WithParamInterface<
                          std::tuple<int, int, int, int>> {};

TEST_P(MoEConfigTest, VariousConfigurations) {
    auto [batch_size, d_model, num_experts, top_k] = GetParam();
    int d_ff = d_model * 4;  // Standard 4x expansion

    auto input = randomVector(batch_size * d_model, 0.1f);
    auto gate_weights = randomVector(num_experts * d_model, 0.1f);
    auto W1 = randomVector(num_experts * d_ff * d_model, 0.1f);
    auto b1 = randomVector(num_experts * d_ff, 0.1f);
    auto W2 = randomVector(num_experts * d_model * d_ff, 0.1f);
    auto b2 = randomVector(num_experts * d_model, 0.1f);

    std::vector<float> output_naive(batch_size * d_model);
    std::vector<float> output_parallel(batch_size * d_model);

    // Run naive
    cpu_moe_forward(output_naive.data(), input.data(), gate_weights.data(),
                   W1.data(), b1.data(), W2.data(), b2.data(),
                   batch_size, d_model, d_ff, num_experts, top_k);

    // Run parallel
    cpu_moe_forward_parallel(output_parallel.data(), input.data(), gate_weights.data(),
                            W1.data(), b1.data(), W2.data(), b2.data(),
                            batch_size, d_model, d_ff, num_experts, top_k, -1);

    // Compare
    float max_diff = maxAbsDiff(output_naive.data(), output_parallel.data(),
                                 batch_size * d_model);
    EXPECT_LT(max_diff, 1e-3f)
        << "Config (B=" << batch_size << ", D=" << d_model
        << ", E=" << num_experts << ", K=" << top_k
        << ") max diff: " << max_diff;
}

INSTANTIATE_TEST_SUITE_P(
    ConfigVariations,
    MoEConfigTest,
    ::testing::Values(
        // (batch_size, d_model, num_experts, top_k)
        std::make_tuple(4, 8, 4, 1),
        std::make_tuple(8, 16, 4, 2),
        std::make_tuple(16, 32, 8, 2),
        std::make_tuple(8, 64, 8, 1),
        std::make_tuple(4, 32, 16, 2)
    )
);

// ============================================================
// Performance Benchmark Test
// ============================================================

/**
 * @brief Performance benchmark for MoE forward pass
 */
TEST_F(CPUExpertsTest, PerformanceBenchmark) {
    const int batch_size = 32;
    const int d_model = 128;
    const int d_ff = 512;
    const int num_experts = 8;
    const int top_k = 2;

    auto input = randomVector(batch_size * d_model, 0.1f);
    auto gate_weights = randomVector(num_experts * d_model, 0.1f);
    auto W1 = randomVector(num_experts * d_ff * d_model, 0.1f);
    auto b1 = randomVector(num_experts * d_ff, 0.1f);
    auto W2 = randomVector(num_experts * d_model * d_ff, 0.1f);
    auto b2 = randomVector(num_experts * d_model, 0.1f);

    std::vector<float> output(batch_size * d_model);

    float time_ms = cpu_moe_timed(output.data(), input.data(), gate_weights.data(),
                                  W1.data(), b1.data(), W2.data(), b2.data(),
                                  batch_size, d_model, d_ff, num_experts, top_k,
                                  "naive");

    // Calculate GFLOPS
    double gate_flops = 2.0 * batch_size * num_experts * d_model;
    double expert_flops = 2.0 * batch_size * top_k * 2 * d_model * d_ff;
    double total_flops = gate_flops + expert_flops;
    double gflops = (total_flops / (time_ms / 1000.0)) / 1e9;

    std::cout << "MoE Configuration: B=" << batch_size
              << ", D=" << d_model << ", FF=" << d_ff
              << ", E=" << num_experts << ", K=" << top_k << std::endl;
    std::cout << "Time: " << time_ms << " ms" << std::endl;
    std::cout << "Performance: " << gflops << " GFLOPS" << std::endl;
    std::cout << "Sparsity: " << (1.0 - (double)top_k / num_experts) * 100 << "%" << std::endl;

    // Sanity check: should complete in reasonable time
    EXPECT_GT(gflops, 0.1) << "Performance too low for CPU MoE";
}
