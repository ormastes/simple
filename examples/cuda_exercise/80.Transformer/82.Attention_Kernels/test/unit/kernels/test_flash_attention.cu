/**
 * @file test_flash_attention.cu
 * @brief Unit tests for tiled scaled dot-product attention (FlashAttention-style)
 *
 * Compares the tiled GPU SDPA against a naive CPU reference implementation for both
 * causal and non-causal modes, verifying numerical accuracy within floating-point
 * tolerance.
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include <vector>
#include <cmath>
#include <cfloat>
#include <algorithm>

namespace transformer {
extern void launch_flash_attention(float* output, const float* Q, const float* K, const float* V,
                                    int batch, int num_heads, int seq_len, int head_dim,
                                    bool causal, cudaStream_t stream);
}

/**
 * @brief Test fixture for FlashAttention tests
 */
class FlashAttentionTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }

    /**
     * @brief CPU reference SDPA: O = softmax(QK^T / sqrt(d)) * V
     *
     * Processes a single (batch, head) slice of shape [seq_len, head_dim].
     *
     * @param[out] output  Output [seq_len, head_dim]
     * @param[in]  Q       Query [seq_len, head_dim]
     * @param[in]  K       Key [seq_len, head_dim]
     * @param[in]  V       Value [seq_len, head_dim]
     * @param[in]  seq_len Sequence length
     * @param[in]  head_dim Head dimension
     * @param[in]  causal  Whether to apply causal mask
     */
    void cpu_sdpa(float* output, const float* Q, const float* K, const float* V,
                  int seq_len, int head_dim, bool causal) {
        float scale = 1.0f / std::sqrt(static_cast<float>(head_dim));

        for (int q = 0; q < seq_len; q++) {
            // Compute scores: QK^T * scale
            std::vector<float> scores(seq_len);
            for (int k = 0; k < seq_len; k++) {
                float dot = 0.0f;
                for (int d = 0; d < head_dim; d++) {
                    dot += Q[q * head_dim + d] * K[k * head_dim + d];
                }
                scores[k] = dot * scale;

                // Apply causal mask
                if (causal && k > q) {
                    scores[k] = -FLT_MAX;
                }
            }

            // Softmax
            float max_val = *std::max_element(scores.begin(), scores.end());
            float sum = 0.0f;
            for (int k = 0; k < seq_len; k++) {
                scores[k] = std::exp(scores[k] - max_val);
                sum += scores[k];
            }
            for (int k = 0; k < seq_len; k++) {
                scores[k] /= sum;
            }

            // Compute output: P * V
            for (int d = 0; d < head_dim; d++) {
                float val = 0.0f;
                for (int k = 0; k < seq_len; k++) {
                    val += scores[k] * V[k * head_dim + d];
                }
                output[q * head_dim + d] = val;
            }
        }
    }
};

/**
 * @brief Non-causal SDPA should match CPU reference
 */
TEST_F(FlashAttentionTest, NonCausal_MatchesCPU) {
    const int batch = 1;
    const int num_heads = 1;
    const int seq_len = 8;
    const int head_dim = 4;
    const int slice_size = seq_len * head_dim;
    const int total = batch * num_heads * slice_size;

    // Initialize Q, K, V with simple patterns
    std::vector<float> h_Q(total), h_K(total), h_V(total);
    for (int i = 0; i < total; i++) {
        h_Q[i] = std::sin(static_cast<float>(i) * 0.3f);
        h_K[i] = std::cos(static_cast<float>(i) * 0.2f);
        h_V[i] = static_cast<float>(i) * 0.1f;
    }

    float* d_Q = cuda_malloc<float>(total);
    float* d_K = cuda_malloc<float>(total);
    float* d_V = cuda_malloc<float>(total);
    float* d_out = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_Q, h_Q.data(), total * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_K, h_K.data(), total * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_V, h_V.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    transformer::launch_flash_attention(d_out, d_Q, d_K, d_V,
                                         batch, num_heads, seq_len, head_dim,
                                         false, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_out(total);
    CHECK_CUDA(cudaMemcpy(h_out.data(), d_out, total * sizeof(float), cudaMemcpyDeviceToHost));

    // CPU reference
    std::vector<float> expected(total);
    cpu_sdpa(expected.data(), h_Q.data(), h_K.data(), h_V.data(),
             seq_len, head_dim, false);

    for (int i = 0; i < total; i++) {
        EXPECT_NEAR(h_out[i], expected[i], 1e-4f)
            << "Non-causal mismatch at index " << i;
    }

    cuda_free(d_Q);
    cuda_free(d_K);
    cuda_free(d_V);
    cuda_free(d_out);
}

/**
 * @brief Causal SDPA should match CPU reference with causal mask
 */
TEST_F(FlashAttentionTest, Causal_MatchesCPU) {
    const int batch = 1;
    const int num_heads = 1;
    const int seq_len = 8;
    const int head_dim = 4;
    const int slice_size = seq_len * head_dim;
    const int total = batch * num_heads * slice_size;

    std::vector<float> h_Q(total), h_K(total), h_V(total);
    for (int i = 0; i < total; i++) {
        h_Q[i] = std::sin(static_cast<float>(i) * 0.3f);
        h_K[i] = std::cos(static_cast<float>(i) * 0.2f);
        h_V[i] = static_cast<float>(i) * 0.1f;
    }

    float* d_Q = cuda_malloc<float>(total);
    float* d_K = cuda_malloc<float>(total);
    float* d_V = cuda_malloc<float>(total);
    float* d_out = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_Q, h_Q.data(), total * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_K, h_K.data(), total * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_V, h_V.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    transformer::launch_flash_attention(d_out, d_Q, d_K, d_V,
                                         batch, num_heads, seq_len, head_dim,
                                         true, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_out(total);
    CHECK_CUDA(cudaMemcpy(h_out.data(), d_out, total * sizeof(float), cudaMemcpyDeviceToHost));

    // CPU reference with causal mask
    std::vector<float> expected(total);
    cpu_sdpa(expected.data(), h_Q.data(), h_K.data(), h_V.data(),
             seq_len, head_dim, true);

    for (int i = 0; i < total; i++) {
        EXPECT_NEAR(h_out[i], expected[i], 1e-4f)
            << "Causal mismatch at index " << i;
    }

    cuda_free(d_Q);
    cuda_free(d_K);
    cuda_free(d_V);
    cuda_free(d_out);
}

/**
 * @brief Causal mask: first query position should only attend to itself
 *
 * With causal masking, q=0 can only attend to k=0, so output[0] should equal V[0].
 */
TEST_F(FlashAttentionTest, Causal_FirstPosition_AttendsOnlySelf) {
    const int batch = 1;
    const int num_heads = 1;
    const int seq_len = 4;
    const int head_dim = 4;
    const int total = batch * num_heads * seq_len * head_dim;

    std::vector<float> h_Q(total, 1.0f);
    std::vector<float> h_K(total, 1.0f);
    std::vector<float> h_V(total);
    // Set V with distinct rows
    for (int t = 0; t < seq_len; t++) {
        for (int d = 0; d < head_dim; d++) {
            h_V[t * head_dim + d] = static_cast<float>(t * 10 + d);
        }
    }

    float* d_Q = cuda_malloc<float>(total);
    float* d_K = cuda_malloc<float>(total);
    float* d_V = cuda_malloc<float>(total);
    float* d_out = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_Q, h_Q.data(), total * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_K, h_K.data(), total * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_V, h_V.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    transformer::launch_flash_attention(d_out, d_Q, d_K, d_V,
                                         batch, num_heads, seq_len, head_dim,
                                         true, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_out(total);
    CHECK_CUDA(cudaMemcpy(h_out.data(), d_out, total * sizeof(float), cudaMemcpyDeviceToHost));

    // First query position (q=0) with causal mask: softmax over single element = 1.0
    // So output[0,:] = V[0,:]
    for (int d = 0; d < head_dim; d++) {
        EXPECT_NEAR(h_out[d], h_V[d], 1e-4f)
            << "First position output should equal V[0] at dim " << d;
    }

    cuda_free(d_Q);
    cuda_free(d_K);
    cuda_free(d_V);
    cuda_free(d_out);
}

/**
 * @brief Multi-head attention should process heads independently
 */
TEST_F(FlashAttentionTest, MultiHead_IndependentProcessing) {
    const int batch = 1;
    const int num_heads = 2;
    const int seq_len = 4;
    const int head_dim = 4;
    const int slice = seq_len * head_dim;
    const int total = batch * num_heads * slice;

    // Set both heads to the same Q, K, V values
    std::vector<float> h_Q(total), h_K(total), h_V(total);
    for (int h = 0; h < num_heads; h++) {
        for (int i = 0; i < slice; i++) {
            h_Q[h * slice + i] = std::sin(static_cast<float>(i) * 0.5f);
            h_K[h * slice + i] = std::cos(static_cast<float>(i) * 0.3f);
            h_V[h * slice + i] = static_cast<float>(i) * 0.1f;
        }
    }

    float* d_Q = cuda_malloc<float>(total);
    float* d_K = cuda_malloc<float>(total);
    float* d_V = cuda_malloc<float>(total);
    float* d_out = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_Q, h_Q.data(), total * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_K, h_K.data(), total * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_V, h_V.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    transformer::launch_flash_attention(d_out, d_Q, d_K, d_V,
                                         batch, num_heads, seq_len, head_dim,
                                         false, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_out(total);
    CHECK_CUDA(cudaMemcpy(h_out.data(), d_out, total * sizeof(float), cudaMemcpyDeviceToHost));

    // Both heads should produce the same output (same input)
    for (int i = 0; i < slice; i++) {
        EXPECT_NEAR(h_out[i], h_out[slice + i], 1e-5f)
            << "Heads should match at index " << i;
    }

    cuda_free(d_Q);
    cuda_free(d_K);
    cuda_free(d_V);
    cuda_free(d_out);
}

/**
 * @brief Multi-batch processing: each batch element should be independent
 */
TEST_F(FlashAttentionTest, MultiBatch_IndependentProcessing) {
    const int batch = 2;
    const int num_heads = 1;
    const int seq_len = 4;
    const int head_dim = 4;
    const int slice = num_heads * seq_len * head_dim;
    const int total = batch * slice;

    // Set both batch elements to the same values
    std::vector<float> h_Q(total), h_K(total), h_V(total);
    for (int b = 0; b < batch; b++) {
        for (int i = 0; i < slice; i++) {
            h_Q[b * slice + i] = std::sin(static_cast<float>(i) * 0.4f);
            h_K[b * slice + i] = std::cos(static_cast<float>(i) * 0.3f);
            h_V[b * slice + i] = static_cast<float>(i) * 0.2f;
        }
    }

    float* d_Q = cuda_malloc<float>(total);
    float* d_K = cuda_malloc<float>(total);
    float* d_V = cuda_malloc<float>(total);
    float* d_out = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_Q, h_Q.data(), total * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_K, h_K.data(), total * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_V, h_V.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    transformer::launch_flash_attention(d_out, d_Q, d_K, d_V,
                                         batch, num_heads, seq_len, head_dim,
                                         false, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_out(total);
    CHECK_CUDA(cudaMemcpy(h_out.data(), d_out, total * sizeof(float), cudaMemcpyDeviceToHost));

    // Both batch elements should produce the same output
    for (int i = 0; i < slice; i++) {
        EXPECT_NEAR(h_out[i], h_out[slice + i], 1e-5f)
            << "Batch elements should match at index " << i;
    }

    cuda_free(d_Q);
    cuda_free(d_K);
    cuda_free(d_V);
    cuda_free(d_out);
}
