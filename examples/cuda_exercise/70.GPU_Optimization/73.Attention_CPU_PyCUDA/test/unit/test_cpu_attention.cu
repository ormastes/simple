/**
 * @file test_cpu_attention.cu
 * @brief Unit tests for CPU attention mechanisms
 *
 * Tests cover scaled dot-product attention (naive and causal),
 * softmax correctness, multi-head attention, parallel correctness,
 * and parameterized size variations.
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cpu_attention.h"
#include <vector>
#include <random>
#include <cmath>
#include <numeric>

/**
 * @brief Test fixture for CPU Attention tests
 *
 * Provides helper utilities for generating random matrices,
 * computing reference attention, and comparing results.
 */
class CPUAttentionTest : public ::testing::Test {
protected:
    void SetUp() override {
        gen.seed(42);
    }

    std::mt19937 gen;

    /// Generate a random matrix of given dimensions
    std::vector<float> randomMatrix(int rows, int cols) {
        std::vector<float> mat(rows * cols);
        std::uniform_real_distribution<float> dist(-1.0f, 1.0f);
        for (auto& val : mat) {
            val = dist(gen);
        }
        return mat;
    }

    /// Compute reference SDPA: softmax(Q*K^T / sqrt(d_k)) * V
    std::vector<float> referenceSDPA(const float* Q, const float* K, const float* V,
                                      int seq_len, int d_model, bool causal = false) {
        float scale = 1.0f / sqrtf(static_cast<float>(d_model));

        // scores = Q * K^T
        std::vector<float> scores(seq_len * seq_len);
        for (int i = 0; i < seq_len; i++) {
            for (int j = 0; j < seq_len; j++) {
                float dot = 0.0f;
                for (int d = 0; d < d_model; d++) {
                    dot += Q[i * d_model + d] * K[j * d_model + d];
                }
                scores[i * seq_len + j] = dot * scale;

                // Apply causal mask
                if (causal && j > i) {
                    scores[i * seq_len + j] = -INFINITY;
                }
            }
        }

        // Softmax row-wise
        for (int i = 0; i < seq_len; i++) {
            float max_val = scores[i * seq_len];
            for (int j = 1; j < seq_len; j++) {
                max_val = std::max(max_val, scores[i * seq_len + j]);
            }

            float sum_exp = 0.0f;
            for (int j = 0; j < seq_len; j++) {
                scores[i * seq_len + j] = expf(scores[i * seq_len + j] - max_val);
                sum_exp += scores[i * seq_len + j];
            }

            for (int j = 0; j < seq_len; j++) {
                scores[i * seq_len + j] /= sum_exp;
            }
        }

        // output = scores * V
        std::vector<float> output(seq_len * d_model);
        for (int i = 0; i < seq_len; i++) {
            for (int d = 0; d < d_model; d++) {
                float sum = 0.0f;
                for (int j = 0; j < seq_len; j++) {
                    sum += scores[i * seq_len + j] * V[j * d_model + d];
                }
                output[i * d_model + d] = sum;
            }
        }

        return output;
    }

    /// Compare two float arrays with tolerance
    bool matricesEqual(const float* A, const float* B, int size, float tol = 1e-4f) {
        for (int i = 0; i < size; i++) {
            if (std::abs(A[i] - B[i]) > tol) {
                return false;
            }
        }
        return true;
    }

    /// Get the attention scores for causal SDPA (for mask verification)
    std::vector<float> getCausalScores(const float* Q, const float* K,
                                        int seq_len, int d_model) {
        float scale = 1.0f / sqrtf(static_cast<float>(d_model));
        std::vector<float> scores(seq_len * seq_len);
        for (int i = 0; i < seq_len; i++) {
            for (int j = 0; j < seq_len; j++) {
                float dot = 0.0f;
                for (int d = 0; d < d_model; d++) {
                    dot += Q[i * d_model + d] * K[j * d_model + d];
                }
                scores[i * seq_len + j] = dot * scale;
                if (j > i) {
                    scores[i * seq_len + j] = -INFINITY;
                }
            }
        }
        // Softmax
        for (int i = 0; i < seq_len; i++) {
            float max_val = scores[i * seq_len];
            for (int j = 1; j < seq_len; j++) {
                max_val = std::max(max_val, scores[i * seq_len + j]);
            }
            float sum_exp = 0.0f;
            for (int j = 0; j < seq_len; j++) {
                scores[i * seq_len + j] = expf(scores[i * seq_len + j] - max_val);
                sum_exp += scores[i * seq_len + j];
            }
            for (int j = 0; j < seq_len; j++) {
                scores[i * seq_len + j] /= sum_exp;
            }
        }
        return scores;
    }
};

/**
 * @brief Test SDPA naive correctness against reference implementation
 */
TEST_F(CPUAttentionTest, SDPACorrectness) {
    const int seq_len = 32, d_model = 16;

    auto Q = randomMatrix(seq_len, d_model);
    auto K = randomMatrix(seq_len, d_model);
    auto V = randomMatrix(seq_len, d_model);
    std::vector<float> output(seq_len * d_model);

    cpu_sdpa_naive(output.data(), Q.data(), K.data(), V.data(), seq_len, d_model);

    auto ref = referenceSDPA(Q.data(), K.data(), V.data(), seq_len, d_model, false);

    EXPECT_TRUE(matricesEqual(output.data(), ref.data(), seq_len * d_model))
        << "SDPA naive output does not match reference";
}

/**
 * @brief Verify causal mask: future token attention weights should be ~0
 *
 * For causal attention, position i should not attend to position j > i.
 * After softmax, the weights for masked positions should be essentially zero.
 */
TEST_F(CPUAttentionTest, CausalMask) {
    const int seq_len = 16, d_model = 8;

    auto Q = randomMatrix(seq_len, d_model);
    auto K = randomMatrix(seq_len, d_model);
    auto V = randomMatrix(seq_len, d_model);
    std::vector<float> output(seq_len * d_model);

    cpu_sdpa_causal(output.data(), Q.data(), K.data(), V.data(), seq_len, d_model);

    auto ref = referenceSDPA(Q.data(), K.data(), V.data(), seq_len, d_model, true);

    EXPECT_TRUE(matricesEqual(output.data(), ref.data(), seq_len * d_model))
        << "Causal SDPA output does not match reference";

    // Additionally verify that the attention pattern is lower-triangular:
    // The causal output for row i should only depend on V[0..i], not V[i+1..].
    // We verify this by checking that causal output for row 0 equals
    // a weighted version of only V[0].
    // For row 0: only j=0 has non-zero attention weight (it must be 1.0 after softmax)
    for (int d = 0; d < d_model; d++) {
        EXPECT_NEAR(output[0 * d_model + d], V[0 * d_model + d], 1e-5f)
            << "Row 0 of causal attention should exactly equal V[0] "
            << "(only token attends to itself)";
    }
}

/**
 * @brief Verify softmax correctness: each row should sum to 1.0
 */
TEST_F(CPUAttentionTest, SoftmaxCorrectness) {
    const int rows = 16, cols = 32;

    auto input = randomMatrix(rows, cols);
    std::vector<float> output(rows * cols);

    cpu_softmax(output.data(), input.data(), rows, cols);

    for (int i = 0; i < rows; i++) {
        float row_sum = 0.0f;
        for (int j = 0; j < cols; j++) {
            float val = output[i * cols + j];
            EXPECT_GE(val, 0.0f) << "Softmax output should be non-negative";
            row_sum += val;
        }
        EXPECT_NEAR(row_sum, 1.0f, 1e-5f)
            << "Softmax row " << i << " does not sum to 1.0";
    }
}

/**
 * @brief Verify softmax handles extreme values (numerical stability)
 */
TEST_F(CPUAttentionTest, SoftmaxNumericalStability) {
    const int rows = 4, cols = 4;

    // Large values that would overflow naive exp()
    std::vector<float> input = {
        100.0f, 200.0f, 300.0f, 400.0f,
        -100.0f, -200.0f, -300.0f, -400.0f,
        0.0f, 0.0f, 0.0f, 0.0f,
        1000.0f, 1000.0f, 1000.0f, 1000.0f
    };
    std::vector<float> output(rows * cols);

    cpu_softmax(output.data(), input.data(), rows, cols);

    for (int i = 0; i < rows; i++) {
        float row_sum = 0.0f;
        for (int j = 0; j < cols; j++) {
            float val = output[i * cols + j];
            EXPECT_FALSE(std::isnan(val)) << "Softmax produced NaN at row " << i << ", col " << j;
            EXPECT_FALSE(std::isinf(val)) << "Softmax produced Inf at row " << i << ", col " << j;
            EXPECT_GE(val, 0.0f);
            row_sum += val;
        }
        EXPECT_NEAR(row_sum, 1.0f, 1e-5f);
    }

    // Equal inputs should produce uniform distribution
    for (int j = 0; j < cols; j++) {
        EXPECT_NEAR(output[2 * cols + j], 0.25f, 1e-5f)
            << "Equal inputs should produce uniform softmax";
        EXPECT_NEAR(output[3 * cols + j], 0.25f, 1e-5f)
            << "Equal large inputs should produce uniform softmax";
    }
}

/**
 * @brief Test multi-head attention output dimensions and basic correctness
 */
TEST_F(CPUAttentionTest, MultiHeadAttention) {
    const int batch_size = 2, seq_len = 16, d_model = 32, num_heads = 4;

    auto Q = randomMatrix(batch_size * seq_len, d_model);
    auto K = randomMatrix(batch_size * seq_len, d_model);
    auto V = randomMatrix(batch_size * seq_len, d_model);

    // W_O as identity-like matrix for simple verification
    std::vector<float> W_O(d_model * d_model, 0.0f);
    for (int i = 0; i < d_model; i++) {
        W_O[i * d_model + i] = 1.0f;  // Identity
    }

    std::vector<float> output(batch_size * seq_len * d_model);

    cpu_multi_head_attention(output.data(), Q.data(), K.data(), V.data(),
                            W_O.data(), batch_size, seq_len, d_model, num_heads);

    // With identity W_O, output should equal concatenated per-head SDPA outputs
    // Verify output is not all zeros (basic sanity check)
    float max_abs = 0.0f;
    for (int i = 0; i < batch_size * seq_len * d_model; i++) {
        max_abs = std::max(max_abs, std::abs(output[i]));
    }
    EXPECT_GT(max_abs, 0.0f) << "Multi-head attention output should not be all zeros";

    // Verify output has finite values
    for (int i = 0; i < batch_size * seq_len * d_model; i++) {
        EXPECT_FALSE(std::isnan(output[i])) << "Output contains NaN at index " << i;
        EXPECT_FALSE(std::isinf(output[i])) << "Output contains Inf at index " << i;
    }
}

/**
 * @brief Test that multi-head with identity W_O and 1 head matches single-head SDPA
 */
TEST_F(CPUAttentionTest, MultiHeadSingleHeadEquivalence) {
    const int batch_size = 1, seq_len = 16, d_model = 16, num_heads = 1;

    auto Q = randomMatrix(seq_len, d_model);
    auto K = randomMatrix(seq_len, d_model);
    auto V = randomMatrix(seq_len, d_model);

    // Identity W_O
    std::vector<float> W_O(d_model * d_model, 0.0f);
    for (int i = 0; i < d_model; i++) {
        W_O[i * d_model + i] = 1.0f;
    }

    std::vector<float> mha_output(seq_len * d_model);
    std::vector<float> sdpa_output(seq_len * d_model);

    cpu_multi_head_attention(mha_output.data(), Q.data(), K.data(), V.data(),
                            W_O.data(), batch_size, seq_len, d_model, num_heads);

    cpu_sdpa_naive(sdpa_output.data(), Q.data(), K.data(), V.data(), seq_len, d_model);

    EXPECT_TRUE(matricesEqual(mha_output.data(), sdpa_output.data(), seq_len * d_model, 1e-4f))
        << "MHA with 1 head and identity W_O should match single-head SDPA";
}

/**
 * @brief Test parallel SDPA matches naive SDPA
 */
TEST_F(CPUAttentionTest, ParallelCorrectness) {
    const int seq_len = 64, d_model = 32;

    auto Q = randomMatrix(seq_len, d_model);
    auto K = randomMatrix(seq_len, d_model);
    auto V = randomMatrix(seq_len, d_model);

    std::vector<float> naive_output(seq_len * d_model);
    std::vector<float> parallel_output(seq_len * d_model);

    cpu_sdpa_naive(naive_output.data(), Q.data(), K.data(), V.data(), seq_len, d_model);
    cpu_sdpa_parallel(parallel_output.data(), Q.data(), K.data(), V.data(), seq_len, d_model, 4);

    EXPECT_TRUE(matricesEqual(naive_output.data(), parallel_output.data(), seq_len * d_model))
        << "Parallel SDPA should produce same results as naive SDPA";
}

/**
 * @brief Test with identity-like Q, K (scores should be identity-like)
 */
TEST_F(CPUAttentionTest, IdentityAttention) {
    const int seq_len = 4, d_model = 4;

    // Q = K = identity-like rows with very large values to make attention sharp
    // When Q[i] is very similar to K[i] and very different from K[j!=i],
    // the attention should approximately select V[i] for each row
    std::vector<float> Q(seq_len * d_model, 0.0f);
    std::vector<float> K(seq_len * d_model, 0.0f);

    // Make each Q[i] and K[i] a one-hot with large magnitude
    for (int i = 0; i < seq_len; i++) {
        Q[i * d_model + i] = 100.0f;
        K[i * d_model + i] = 100.0f;
    }

    // V = sequential values for easy verification
    std::vector<float> V = {
        1, 2, 3, 4,
        5, 6, 7, 8,
        9, 10, 11, 12,
        13, 14, 15, 16
    };

    std::vector<float> output(seq_len * d_model);
    cpu_sdpa_naive(output.data(), Q.data(), K.data(), V.data(), seq_len, d_model);

    // With sharp attention, output[i] should be close to V[i]
    for (int i = 0; i < seq_len; i++) {
        for (int d = 0; d < d_model; d++) {
            EXPECT_NEAR(output[i * d_model + d], V[i * d_model + d], 0.5f)
                << "With sharp attention, output[" << i << "][" << d << "] should be close to V[" << i << "][" << d << "]";
        }
    }
}

/**
 * @brief Parameterized test for various (seq_len, d_model) combinations
 */
class AttentionSizeTest : public CPUAttentionTest,
                           public ::testing::WithParamInterface<std::tuple<int, int>> {};

TEST_P(AttentionSizeTest, VariousSizes) {
    auto [seq_len, d_model] = GetParam();

    auto Q = randomMatrix(seq_len, d_model);
    auto K = randomMatrix(seq_len, d_model);
    auto V = randomMatrix(seq_len, d_model);
    std::vector<float> output(seq_len * d_model);

    cpu_sdpa_naive(output.data(), Q.data(), K.data(), V.data(), seq_len, d_model);

    auto ref = referenceSDPA(Q.data(), K.data(), V.data(), seq_len, d_model, false);

    EXPECT_TRUE(matricesEqual(output.data(), ref.data(), seq_len * d_model))
        << "SDPA failed for seq_len=" << seq_len << ", d_model=" << d_model;
}

INSTANTIATE_TEST_SUITE_P(
    SizeVariations,
    AttentionSizeTest,
    ::testing::Values(
        std::make_tuple(8, 8),
        std::make_tuple(16, 16),
        std::make_tuple(32, 32),
        std::make_tuple(64, 64),
        std::make_tuple(32, 16),
        std::make_tuple(16, 64),
        std::make_tuple(128, 32)
    )
);

/**
 * @brief Performance benchmark test for attention
 */
TEST_F(CPUAttentionTest, PerformanceBenchmark) {
    const int seq_len = 256, d_model = 64;

    auto Q = randomMatrix(seq_len, d_model);
    auto K = randomMatrix(seq_len, d_model);
    auto V = randomMatrix(seq_len, d_model);
    std::vector<float> output(seq_len * d_model);

    float time_ms = cpu_attention_timed(output.data(), Q.data(), K.data(), V.data(),
                                        seq_len, d_model, "naive");

    // Calculate GFLOPS: 4*L*L*D + 5*L*L
    double flops = 4.0 * seq_len * seq_len * d_model + 5.0 * seq_len * seq_len;
    double gflops = (flops / (time_ms / 1000.0)) / 1e9;

    std::cout << "Attention benchmark (seq_len=" << seq_len << ", d_model=" << d_model << ")" << std::endl;
    std::cout << "Time: " << time_ms << " ms" << std::endl;
    std::cout << "Performance: " << gflops << " GFLOPS" << std::endl;

    // Sanity check: CPU attention typically achieves at least 0.1 GFLOPS
    EXPECT_GT(gflops, 0.1) << "Performance too low for CPU attention";
}
