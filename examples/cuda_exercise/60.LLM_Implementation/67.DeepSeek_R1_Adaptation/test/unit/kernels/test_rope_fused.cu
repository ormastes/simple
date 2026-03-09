/**
 * @file test_rope_fused.cu
 * @brief Unit tests for Rotary Position Embeddings (RoPE)
 *
 * Tests RoPE correctness by verifying that rotations preserve vector norms,
 * different positions produce different embeddings, and the precomputed
 * frequency table matches inline computation.
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/rope_embeddings.h"
#include "common/deepseek_config.h"
#include "cuda_utils.h"
#include <vector>
#include <cmath>

namespace llm {

class RoPETest : public GpuTest {
protected:
    RoPEConfig rope_config;
    int batch_size = 1;
    int seq_len = 16;
    int num_heads = 8;
    int num_kv_heads = 2;
    int head_dim = 8;  // Small for testing

    void SetUp() override {
        GpuTest::SetUp();
        rope_config = RoPEConfig(10000.0f, head_dim, 128);
    }
};

TEST_F(RoPETest, PreservesNorm) {
    // RoPE is a rotation, so it should preserve the L2 norm of each head vector
    int q_total = batch_size * seq_len * num_heads * head_dim;
    int k_total = batch_size * seq_len * num_kv_heads * head_dim;

    float *d_Q = nullptr, *d_K = nullptr;
    CHECK_CUDA(cudaMalloc(&d_Q, q_total * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_K, k_total * sizeof(float)));

    // Fill with known values
    std::vector<float> h_Q(q_total), h_K(k_total);
    for (int i = 0; i < q_total; ++i) h_Q[i] = 0.1f * (i % 7 - 3);
    for (int i = 0; i < k_total; ++i) h_K[i] = 0.1f * (i % 5 - 2);

    // Compute norms before RoPE
    auto compute_head_norms = [](const std::vector<float>& data, int num_heads_local,
                                  int head_dim_local, int seq, int batch) {
        std::vector<float> norms;
        int stride = num_heads_local * head_dim_local;
        for (int b = 0; b < batch; ++b) {
            for (int s = 0; s < seq; ++s) {
                for (int h = 0; h < num_heads_local; ++h) {
                    float norm = 0.0f;
                    int base = b * seq * stride + s * stride + h * head_dim_local;
                    for (int d = 0; d < head_dim_local; ++d) {
                        norm += data[base + d] * data[base + d];
                    }
                    norms.push_back(std::sqrt(norm));
                }
            }
        }
        return norms;
    };

    auto q_norms_before = compute_head_norms(h_Q, num_heads, head_dim, seq_len, batch_size);
    auto k_norms_before = compute_head_norms(h_K, num_kv_heads, head_dim, seq_len, batch_size);

    CHECK_CUDA(cudaMemcpy(d_Q, h_Q.data(), q_total * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_K, h_K.data(), k_total * sizeof(float), cudaMemcpyHostToDevice));

    // Apply RoPE
    rope_forward(d_Q, d_K, rope_config, batch_size, seq_len,
                 num_heads, num_kv_heads);

    // Read back
    CHECK_CUDA(cudaMemcpy(h_Q.data(), d_Q, q_total * sizeof(float), cudaMemcpyDeviceToHost));
    CHECK_CUDA(cudaMemcpy(h_K.data(), d_K, k_total * sizeof(float), cudaMemcpyDeviceToHost));

    auto q_norms_after = compute_head_norms(h_Q, num_heads, head_dim, seq_len, batch_size);
    auto k_norms_after = compute_head_norms(h_K, num_kv_heads, head_dim, seq_len, batch_size);

    // Norms should be preserved (rotation is norm-preserving)
    for (size_t i = 0; i < q_norms_before.size(); ++i) {
        EXPECT_NEAR(q_norms_before[i], q_norms_after[i], 1e-4f)
            << "Q head norm changed at index " << i;
    }
    for (size_t i = 0; i < k_norms_before.size(); ++i) {
        EXPECT_NEAR(k_norms_before[i], k_norms_after[i], 1e-4f)
            << "K head norm changed at index " << i;
    }

    cudaFree(d_Q);
    cudaFree(d_K);
}

TEST_F(RoPETest, DifferentPositionsDifferentEmbeddings) {
    // Identical vectors at different positions should produce different results after RoPE
    int q_total = batch_size * seq_len * num_heads * head_dim;
    int k_total = batch_size * seq_len * num_kv_heads * head_dim;

    float *d_Q = nullptr, *d_K = nullptr;
    CHECK_CUDA(cudaMalloc(&d_Q, q_total * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_K, k_total * sizeof(float)));

    // Fill all positions with the same vector
    std::vector<float> h_Q(q_total);
    std::vector<float> h_K(k_total);
    int q_stride = num_heads * head_dim;
    int k_stride = num_kv_heads * head_dim;
    for (int s = 0; s < seq_len; ++s) {
        for (int j = 0; j < q_stride; ++j) h_Q[s * q_stride + j] = 1.0f;
        for (int j = 0; j < k_stride; ++j) h_K[s * k_stride + j] = 1.0f;
    }

    CHECK_CUDA(cudaMemcpy(d_Q, h_Q.data(), q_total * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_K, h_K.data(), k_total * sizeof(float), cudaMemcpyHostToDevice));

    rope_forward(d_Q, d_K, rope_config, batch_size, seq_len,
                 num_heads, num_kv_heads);

    CHECK_CUDA(cudaMemcpy(h_Q.data(), d_Q, q_total * sizeof(float), cudaMemcpyDeviceToHost));

    // Compare position 0 head 0 with position 1 head 0
    bool different = false;
    for (int d = 0; d < head_dim; ++d) {
        if (std::abs(h_Q[d] - h_Q[q_stride + d]) > 1e-6f) {
            different = true;
            break;
        }
    }
    EXPECT_TRUE(different) << "RoPE should produce different results at different positions";

    cudaFree(d_Q);
    cudaFree(d_K);
}

TEST_F(RoPETest, PrecomputeFreqsMatchesInline) {
    // Verify that precomputed cos/sin tables match the inline computation
    int half_head = head_dim / 2;
    int max_seq = rope_config.max_seq_len;

    float *d_cos = nullptr, *d_sin = nullptr;
    CHECK_CUDA(cudaMalloc(&d_cos, max_seq * half_head * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_sin, max_seq * half_head * sizeof(float)));

    rope_precompute_freqs(d_cos, d_sin, rope_config);

    std::vector<float> h_cos(max_seq * half_head), h_sin(max_seq * half_head);
    CHECK_CUDA(cudaMemcpy(h_cos.data(), d_cos, h_cos.size() * sizeof(float), cudaMemcpyDeviceToHost));
    CHECK_CUDA(cudaMemcpy(h_sin.data(), d_sin, h_sin.size() * sizeof(float), cudaMemcpyDeviceToHost));

    // Verify against CPU computation
    for (int pos = 0; pos < std::min(max_seq, 32); ++pos) {
        for (int d = 0; d < half_head; ++d) {
            float freq = 1.0f / std::pow(rope_config.theta,
                         (2.0f * d) / static_cast<float>(head_dim));
            float angle = static_cast<float>(pos) * freq;
            float expected_cos = std::cos(angle);
            float expected_sin = std::sin(angle);

            EXPECT_NEAR(h_cos[pos * half_head + d], expected_cos, 1e-5f)
                << "cos mismatch at pos=" << pos << " d=" << d;
            EXPECT_NEAR(h_sin[pos * half_head + d], expected_sin, 1e-5f)
                << "sin mismatch at pos=" << pos << " d=" << d;
        }
    }

    cudaFree(d_cos);
    cudaFree(d_sin);
}

} // namespace llm
