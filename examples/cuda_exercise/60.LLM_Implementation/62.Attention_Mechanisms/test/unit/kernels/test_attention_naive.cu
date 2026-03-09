/**
 * @file test_attention_naive.cu
 * @brief Unit tests for naive self-attention and causal attention kernels
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/self_attention.h"
#include "common/causal_attention.h"
#include "cuda_utils.h"
#include <vector>
#include <cmath>
#include <numeric>
#include <random>

using namespace llm;

/**
 * @brief Test fixture for attention kernel tests with GPU setup
 */
class AttentionNaiveTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }

    /**
     * @brief Helper: compute self-attention on CPU for reference
     *
     * @param Q Query [batch, seq_len, d_model]
     * @param K Key [batch, seq_len, d_model]
     * @param V Value [batch, seq_len, d_model]
     * @param config Attention config
     * @param batch_size Batch size
     * @param seq_len Sequence length
     * @param causal Whether to apply causal mask
     * @return Output [batch, seq_len, d_model]
     */
    std::vector<float> cpu_attention(
        const std::vector<float>& Q,
        const std::vector<float>& K,
        const std::vector<float>& V,
        const AttentionConfig& config,
        int batch_size,
        int seq_len,
        bool causal = false
    ) {
        int d_model = config.d_model;
        int num_heads = config.num_heads;
        int head_dim = config.head_dim;
        float scale = 1.0f / std::sqrt(static_cast<float>(head_dim));

        std::vector<float> output(batch_size * seq_len * d_model, 0.0f);

        for (int b = 0; b < batch_size; ++b) {
            for (int h = 0; h < num_heads; ++h) {
                // Compute QK^T for this head
                std::vector<float> scores(seq_len * seq_len, 0.0f);

                for (int i = 0; i < seq_len; ++i) {
                    for (int j = 0; j < seq_len; ++j) {
                        float dot = 0.0f;
                        for (int k = 0; k < head_dim; ++k) {
                            int q_idx = (b * seq_len + i) * d_model + h * head_dim + k;
                            int k_idx = (b * seq_len + j) * d_model + h * head_dim + k;
                            dot += Q[q_idx] * K[k_idx];
                        }
                        scores[i * seq_len + j] = dot * scale;
                    }
                }

                // Apply causal mask
                if (causal) {
                    for (int i = 0; i < seq_len; ++i) {
                        for (int j = i + 1; j < seq_len; ++j) {
                            scores[i * seq_len + j] = -1e30f;
                        }
                    }
                }

                // Softmax per row
                for (int i = 0; i < seq_len; ++i) {
                    float max_val = -1e30f;
                    for (int j = 0; j < seq_len; ++j) {
                        max_val = std::max(max_val, scores[i * seq_len + j]);
                    }
                    float sum = 0.0f;
                    for (int j = 0; j < seq_len; ++j) {
                        scores[i * seq_len + j] = std::exp(scores[i * seq_len + j] - max_val);
                        sum += scores[i * seq_len + j];
                    }
                    for (int j = 0; j < seq_len; ++j) {
                        scores[i * seq_len + j] /= sum;
                    }
                }

                // Multiply by V
                for (int i = 0; i < seq_len; ++i) {
                    for (int k = 0; k < head_dim; ++k) {
                        float sum = 0.0f;
                        for (int j = 0; j < seq_len; ++j) {
                            int v_idx = (b * seq_len + j) * d_model + h * head_dim + k;
                            sum += scores[i * seq_len + j] * V[v_idx];
                        }
                        int out_idx = (b * seq_len + i) * d_model + h * head_dim + k;
                        output[out_idx] = sum;
                    }
                }
            }
        }
        return output;
    }
};

/**
 * @brief Test self-attention output shape and non-zero values
 */
TEST_F(AttentionNaiveTest, SelfAttention_OutputShape) {
    int batch_size = 1;
    int seq_len = 4;
    int d_model = 8;
    int num_heads = 2;
    AttentionConfig config(d_model, num_heads);

    int total_elements = batch_size * seq_len * d_model;

    // Create Q, K, V with known values
    std::vector<float> h_Q(total_elements);
    std::vector<float> h_K(total_elements);
    std::vector<float> h_V(total_elements);

    // Fill with simple pattern
    for (int i = 0; i < total_elements; ++i) {
        h_Q[i] = static_cast<float>(i % 5) * 0.1f;
        h_K[i] = static_cast<float>((i + 1) % 5) * 0.1f;
        h_V[i] = static_cast<float>((i + 2) % 5) * 0.1f;
    }

    // Copy to device
    float* d_Q = cuda_malloc<float>(total_elements);
    float* d_K = cuda_malloc<float>(total_elements);
    float* d_V = cuda_malloc<float>(total_elements);
    float* d_output = cuda_malloc<float>(total_elements);

    CHECK_CUDA(cudaMemcpy(d_Q, h_Q.data(), total_elements * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_K, h_K.data(), total_elements * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_V, h_V.data(), total_elements * sizeof(float), cudaMemcpyHostToDevice));

    // Run self-attention
    self_attention_forward(d_output, d_Q, d_K, d_V, config, batch_size, seq_len);

    // Copy output back
    std::vector<float> h_output(total_elements);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total_elements * sizeof(float),
                          cudaMemcpyDeviceToHost));

    // Output should have same shape (non-zero values present)
    int non_zero = 0;
    for (float val : h_output) {
        if (std::abs(val) > 1e-8f) non_zero++;
    }
    EXPECT_GT(non_zero, 0) << "Output should contain non-zero values";

    // All values should be finite
    for (int i = 0; i < total_elements; ++i) {
        EXPECT_TRUE(std::isfinite(h_output[i]))
            << "Output[" << i << "] = " << h_output[i] << " is not finite";
    }

    cuda_free(d_Q);
    cuda_free(d_K);
    cuda_free(d_V);
    cuda_free(d_output);
}

/**
 * @brief Test self-attention correctness against CPU reference
 */
TEST_F(AttentionNaiveTest, SelfAttention_CorrectnessVsCPU) {
    int batch_size = 1;
    int seq_len = 4;
    int d_model = 8;
    int num_heads = 2;
    AttentionConfig config(d_model, num_heads);

    int total_elements = batch_size * seq_len * d_model;

    // Create deterministic Q, K, V
    std::vector<float> h_Q(total_elements);
    std::vector<float> h_K(total_elements);
    std::vector<float> h_V(total_elements);

    std::default_random_engine gen(42);
    std::normal_distribution<float> dist(0.0f, 0.5f);
    for (int i = 0; i < total_elements; ++i) {
        h_Q[i] = dist(gen);
        h_K[i] = dist(gen);
        h_V[i] = dist(gen);
    }

    // CPU reference
    std::vector<float> cpu_output = cpu_attention(h_Q, h_K, h_V, config,
                                                   batch_size, seq_len, false);

    // GPU computation
    float* d_Q = cuda_malloc<float>(total_elements);
    float* d_K = cuda_malloc<float>(total_elements);
    float* d_V = cuda_malloc<float>(total_elements);
    float* d_output = cuda_malloc<float>(total_elements);

    CHECK_CUDA(cudaMemcpy(d_Q, h_Q.data(), total_elements * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_K, h_K.data(), total_elements * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_V, h_V.data(), total_elements * sizeof(float), cudaMemcpyHostToDevice));

    self_attention_forward(d_output, d_Q, d_K, d_V, config, batch_size, seq_len);

    std::vector<float> gpu_output(total_elements);
    CHECK_CUDA(cudaMemcpy(gpu_output.data(), d_output, total_elements * sizeof(float),
                          cudaMemcpyDeviceToHost));

    // Compare GPU vs CPU
    for (int i = 0; i < total_elements; ++i) {
        EXPECT_NEAR(gpu_output[i], cpu_output[i], 1e-3f)
            << "Mismatch at index " << i
            << ": GPU=" << gpu_output[i] << " CPU=" << cpu_output[i];
    }

    cuda_free(d_Q);
    cuda_free(d_K);
    cuda_free(d_V);
    cuda_free(d_output);
}

/**
 * @brief Test causal attention masks future tokens
 */
TEST_F(AttentionNaiveTest, CausalAttention_MasksFutureTokens) {
    int batch_size = 1;
    int seq_len = 4;
    int d_model = 4;
    int num_heads = 1;
    AttentionConfig config(d_model, num_heads);

    int total_elements = batch_size * seq_len * d_model;

    // Create Q, K, V where all tokens are identical except the last one
    // The last token has very different values
    std::vector<float> h_Q(total_elements, 0.0f);
    std::vector<float> h_K(total_elements, 0.0f);
    std::vector<float> h_V(total_elements, 0.0f);

    // Set tokens 0..2 to identical values
    for (int s = 0; s < seq_len - 1; ++s) {
        for (int d = 0; d < d_model; ++d) {
            h_Q[s * d_model + d] = 0.5f;
            h_K[s * d_model + d] = 0.5f;
            h_V[s * d_model + d] = 1.0f;
        }
    }
    // Set token 3 (last) to very different values
    for (int d = 0; d < d_model; ++d) {
        h_Q[(seq_len - 1) * d_model + d] = 0.5f;
        h_K[(seq_len - 1) * d_model + d] = 0.5f;
        h_V[(seq_len - 1) * d_model + d] = 100.0f;  // Very large V
    }

    // GPU computation with causal attention
    float* d_Q = cuda_malloc<float>(total_elements);
    float* d_K = cuda_malloc<float>(total_elements);
    float* d_V = cuda_malloc<float>(total_elements);
    float* d_output = cuda_malloc<float>(total_elements);

    CHECK_CUDA(cudaMemcpy(d_Q, h_Q.data(), total_elements * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_K, h_K.data(), total_elements * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_V, h_V.data(), total_elements * sizeof(float), cudaMemcpyHostToDevice));

    causal_attention_forward(d_output, d_Q, d_K, d_V, config, batch_size, seq_len);

    std::vector<float> h_output(total_elements);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total_elements * sizeof(float),
                          cudaMemcpyDeviceToHost));

    // Token 0 (first) can only see itself, so output should be V[0] = 1.0
    for (int d = 0; d < d_model; ++d) {
        EXPECT_NEAR(h_output[0 * d_model + d], 1.0f, 1e-3f)
            << "Token 0 should only attend to itself (V=1.0)";
    }

    // Token 1 can see tokens 0 and 1 (both have V=1.0)
    for (int d = 0; d < d_model; ++d) {
        EXPECT_NEAR(h_output[1 * d_model + d], 1.0f, 1e-3f)
            << "Token 1 should only attend to tokens 0,1 (V=1.0)";
    }

    // Token 2 can see tokens 0,1,2 (all have V=1.0), NOT token 3 (V=100)
    for (int d = 0; d < d_model; ++d) {
        EXPECT_NEAR(h_output[2 * d_model + d], 1.0f, 1e-3f)
            << "Token 2 should NOT see future token 3 (V=100)";
    }

    // Token 3 (last) can see all tokens, output should be a mix
    for (int d = 0; d < d_model; ++d) {
        EXPECT_GT(h_output[3 * d_model + d], 1.0f)
            << "Token 3 should see all tokens including itself (V=100)";
    }

    cuda_free(d_Q);
    cuda_free(d_K);
    cuda_free(d_V);
    cuda_free(d_output);
}

/**
 * @brief Test causal attention correctness against CPU reference
 */
TEST_F(AttentionNaiveTest, CausalAttention_CorrectnessVsCPU) {
    int batch_size = 1;
    int seq_len = 4;
    int d_model = 8;
    int num_heads = 2;
    AttentionConfig config(d_model, num_heads);

    int total_elements = batch_size * seq_len * d_model;

    std::vector<float> h_Q(total_elements);
    std::vector<float> h_K(total_elements);
    std::vector<float> h_V(total_elements);

    std::default_random_engine gen(123);
    std::normal_distribution<float> dist(0.0f, 0.5f);
    for (int i = 0; i < total_elements; ++i) {
        h_Q[i] = dist(gen);
        h_K[i] = dist(gen);
        h_V[i] = dist(gen);
    }

    // CPU reference with causal=true
    std::vector<float> cpu_output = cpu_attention(h_Q, h_K, h_V, config,
                                                   batch_size, seq_len, true);

    // GPU computation
    float* d_Q = cuda_malloc<float>(total_elements);
    float* d_K = cuda_malloc<float>(total_elements);
    float* d_V = cuda_malloc<float>(total_elements);
    float* d_output = cuda_malloc<float>(total_elements);

    CHECK_CUDA(cudaMemcpy(d_Q, h_Q.data(), total_elements * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_K, h_K.data(), total_elements * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_V, h_V.data(), total_elements * sizeof(float), cudaMemcpyHostToDevice));

    causal_attention_forward(d_output, d_Q, d_K, d_V, config, batch_size, seq_len);

    std::vector<float> gpu_output(total_elements);
    CHECK_CUDA(cudaMemcpy(gpu_output.data(), d_output, total_elements * sizeof(float),
                          cudaMemcpyDeviceToHost));

    for (int i = 0; i < total_elements; ++i) {
        EXPECT_NEAR(gpu_output[i], cpu_output[i], 1e-3f)
            << "Causal mismatch at index " << i;
    }

    cuda_free(d_Q);
    cuda_free(d_K);
    cuda_free(d_V);
    cuda_free(d_output);
}

/**
 * @brief Test self-attention with batch > 1
 */
TEST_F(AttentionNaiveTest, SelfAttention_BatchProcessing) {
    int batch_size = 2;
    int seq_len = 4;
    int d_model = 8;
    int num_heads = 2;
    AttentionConfig config(d_model, num_heads);

    int total_elements = batch_size * seq_len * d_model;

    std::vector<float> h_Q(total_elements);
    std::vector<float> h_K(total_elements);
    std::vector<float> h_V(total_elements);

    std::default_random_engine gen(99);
    std::normal_distribution<float> dist(0.0f, 0.3f);
    for (int i = 0; i < total_elements; ++i) {
        h_Q[i] = dist(gen);
        h_K[i] = dist(gen);
        h_V[i] = dist(gen);
    }

    float* d_Q = cuda_malloc<float>(total_elements);
    float* d_K = cuda_malloc<float>(total_elements);
    float* d_V = cuda_malloc<float>(total_elements);
    float* d_output = cuda_malloc<float>(total_elements);

    CHECK_CUDA(cudaMemcpy(d_Q, h_Q.data(), total_elements * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_K, h_K.data(), total_elements * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_V, h_V.data(), total_elements * sizeof(float), cudaMemcpyHostToDevice));

    self_attention_forward(d_output, d_Q, d_K, d_V, config, batch_size, seq_len);

    std::vector<float> h_output(total_elements);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total_elements * sizeof(float),
                          cudaMemcpyDeviceToHost));

    // CPU reference
    std::vector<float> cpu_output = cpu_attention(h_Q, h_K, h_V, config,
                                                   batch_size, seq_len, false);

    for (int i = 0; i < total_elements; ++i) {
        EXPECT_NEAR(h_output[i], cpu_output[i], 1e-3f)
            << "Batch mismatch at index " << i;
    }

    cuda_free(d_Q);
    cuda_free(d_K);
    cuda_free(d_V);
    cuda_free(d_output);
}

/**
 * @brief Test that attention weights (softmax output) sum to 1 per row
 */
TEST_F(AttentionNaiveTest, SelfAttention_SoftmaxRowsSum) {
    // With uniform Q and K, attention weights should be uniform
    int batch_size = 1;
    int seq_len = 4;
    int d_model = 4;
    int num_heads = 1;
    AttentionConfig config(d_model, num_heads);

    int total_elements = batch_size * seq_len * d_model;

    // All Q,K identical => uniform attention weights
    std::vector<float> h_Q(total_elements, 1.0f);
    std::vector<float> h_K(total_elements, 1.0f);
    // V is identity-like: each token has a unique V
    std::vector<float> h_V(total_elements, 0.0f);
    for (int s = 0; s < seq_len; ++s) {
        for (int d = 0; d < d_model; ++d) {
            h_V[s * d_model + d] = (s == d) ? 1.0f : 0.0f;
        }
    }

    float* d_Q = cuda_malloc<float>(total_elements);
    float* d_K = cuda_malloc<float>(total_elements);
    float* d_V = cuda_malloc<float>(total_elements);
    float* d_output = cuda_malloc<float>(total_elements);

    CHECK_CUDA(cudaMemcpy(d_Q, h_Q.data(), total_elements * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_K, h_K.data(), total_elements * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_V, h_V.data(), total_elements * sizeof(float), cudaMemcpyHostToDevice));

    self_attention_forward(d_output, d_Q, d_K, d_V, config, batch_size, seq_len);

    std::vector<float> h_output(total_elements);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total_elements * sizeof(float),
                          cudaMemcpyDeviceToHost));

    // With uniform attention, each output token should be the average of all V values
    // Since V is identity-like: output[s] should be (1/4, 1/4, 1/4, 1/4) for each token
    for (int s = 0; s < seq_len; ++s) {
        float row_sum = 0.0f;
        for (int d = 0; d < d_model; ++d) {
            float expected = 1.0f / seq_len;  // uniform average of identity rows
            EXPECT_NEAR(h_output[s * d_model + d], expected, 1e-3f);
            row_sum += h_output[s * d_model + d];
        }
        // Sum of output across d_model dimensions should also be 1.0
        // (because V rows sum to 1 and attention is uniform)
        EXPECT_NEAR(row_sum, 1.0f, 1e-3f);
    }

    cuda_free(d_Q);
    cuda_free(d_K);
    cuda_free(d_V);
    cuda_free(d_output);
}
