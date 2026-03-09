/**
 * @file test_attention_stages.cu
 * @brief Tests that all attention optimization stages produce identical results.
 *
 * Verifies naive, tiled, and FlashAttention v2 implementations produce
 * consistent outputs, comparing against a CPU reference.
 */
#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "attention/01_naive.h"
#include "attention/02_tiled.h"
#include "attention/03_flash_v2.h"
#include <vector>
#include <random>
#include <cmath>
#include <cfloat>

/**
 * @brief Test fixture for attention stage comparison tests.
 *
 * Provides a CPU reference attention implementation and comparison helpers.
 */
class AttentionStagesTest : public GpuTest {
protected:
    std::mt19937 gen{42};

    std::vector<float> randomVec(int n) {
        std::vector<float> m(n);
        std::uniform_real_distribution<float> dist(-0.5f, 0.5f);
        for (auto& v : m) v = dist(gen);
        return m;
    }

    /// @brief CPU reference scaled dot-product attention
    std::vector<float> cpuAttention(const float* Q, const float* K, const float* V,
                                     int batch, int seq_len, int head_dim) {
        float scale = 1.0f / std::sqrt(static_cast<float>(head_dim));
        std::vector<float> output(batch * seq_len * head_dim, 0.0f);

        for (int b = 0; b < batch; ++b) {
            std::vector<float> scores(seq_len * seq_len);
            for (int i = 0; i < seq_len; ++i)
                for (int j = 0; j < seq_len; ++j) {
                    float dot = 0.0f;
                    for (int d = 0; d < head_dim; ++d)
                        dot += Q[b * seq_len * head_dim + i * head_dim + d] *
                               K[b * seq_len * head_dim + j * head_dim + d];
                    scores[i * seq_len + j] = dot * scale;
                }

            for (int i = 0; i < seq_len; ++i) {
                float max_val = -FLT_MAX;
                for (int j = 0; j < seq_len; ++j)
                    max_val = std::max(max_val, scores[i * seq_len + j]);
                float sum = 0.0f;
                for (int j = 0; j < seq_len; ++j) {
                    scores[i * seq_len + j] = std::exp(scores[i * seq_len + j] - max_val);
                    sum += scores[i * seq_len + j];
                }
                for (int j = 0; j < seq_len; ++j)
                    scores[i * seq_len + j] /= sum;
            }

            for (int i = 0; i < seq_len; ++i)
                for (int d = 0; d < head_dim; ++d) {
                    float s = 0.0f;
                    for (int j = 0; j < seq_len; ++j)
                        s += scores[i * seq_len + j] *
                             V[b * seq_len * head_dim + j * head_dim + d];
                    output[b * seq_len * head_dim + i * head_dim + d] = s;
                }
        }
        return output;
    }

    bool compareVectors(const float* a, const float* b, int n, float tol = 1e-3f) {
        for (int i = 0; i < n; i++)
            if (std::abs(a[i] - b[i]) > tol) return false;
        return true;
    }
};

TEST_F(AttentionStagesTest, NaiveSDPACorrectness) {
    const int batch = 1, seq_len = 32, head_dim = 16;
    auto Q = randomVec(batch * seq_len * head_dim);
    auto K = randomVec(batch * seq_len * head_dim);
    auto V = randomVec(batch * seq_len * head_dim);
    auto ref = cpuAttention(Q.data(), K.data(), V.data(), batch, seq_len, head_dim);

    float *dQ = cuda_malloc<float>(batch * seq_len * head_dim);
    float *dK = cuda_malloc<float>(batch * seq_len * head_dim);
    float *dV = cuda_malloc<float>(batch * seq_len * head_dim);
    float *dO = cuda_malloc<float>(batch * seq_len * head_dim);
    float *dScores = cuda_malloc<float>(batch * seq_len * seq_len);

    cuda_memcpy_h2d(dQ, Q.data(), batch * seq_len * head_dim);
    cuda_memcpy_h2d(dK, K.data(), batch * seq_len * head_dim);
    cuda_memcpy_h2d(dV, V.data(), batch * seq_len * head_dim);

    opt78::attention_naive(dO, dScores, dQ, dK, dV, batch, seq_len, head_dim);
    CHECK_KERNEL_LAUNCH();

    std::vector<float> h_output(batch * seq_len * head_dim);
    cuda_memcpy_d2h(h_output.data(), dO, batch * seq_len * head_dim);

    EXPECT_TRUE(compareVectors(ref.data(), h_output.data(), batch * seq_len * head_dim))
        << "Naive attention differs from CPU reference";

    cuda_free(dQ); cuda_free(dK); cuda_free(dV); cuda_free(dO); cuda_free(dScores);
}

TEST_F(AttentionStagesTest, TiledSDPACorrectness) {
    const int batch = 1, seq_len = 64, head_dim = 32;
    auto Q = randomVec(batch * seq_len * head_dim);
    auto K = randomVec(batch * seq_len * head_dim);
    auto V = randomVec(batch * seq_len * head_dim);
    auto ref = cpuAttention(Q.data(), K.data(), V.data(), batch, seq_len, head_dim);

    float *dQ = cuda_malloc<float>(batch * seq_len * head_dim);
    float *dK = cuda_malloc<float>(batch * seq_len * head_dim);
    float *dV = cuda_malloc<float>(batch * seq_len * head_dim);
    float *dO = cuda_malloc<float>(batch * seq_len * head_dim);
    float *dScores = cuda_malloc<float>(batch * seq_len * seq_len);

    cuda_memcpy_h2d(dQ, Q.data(), batch * seq_len * head_dim);
    cuda_memcpy_h2d(dK, K.data(), batch * seq_len * head_dim);
    cuda_memcpy_h2d(dV, V.data(), batch * seq_len * head_dim);

    opt78::attention_tiled(dO, dScores, dQ, dK, dV, batch, seq_len, head_dim);
    CHECK_KERNEL_LAUNCH();

    std::vector<float> h_output(batch * seq_len * head_dim);
    cuda_memcpy_d2h(h_output.data(), dO, batch * seq_len * head_dim);

    EXPECT_TRUE(compareVectors(ref.data(), h_output.data(), batch * seq_len * head_dim))
        << "Tiled attention differs from CPU reference";

    cuda_free(dQ); cuda_free(dK); cuda_free(dV); cuda_free(dO); cuda_free(dScores);
}

TEST_F(AttentionStagesTest, FlashV2Correctness) {
    const int batch = 2, seq_len = 64, head_dim = 32;
    auto Q = randomVec(batch * seq_len * head_dim);
    auto K = randomVec(batch * seq_len * head_dim);
    auto V = randomVec(batch * seq_len * head_dim);
    auto ref = cpuAttention(Q.data(), K.data(), V.data(), batch, seq_len, head_dim);

    float *dQ = cuda_malloc<float>(batch * seq_len * head_dim);
    float *dK = cuda_malloc<float>(batch * seq_len * head_dim);
    float *dV = cuda_malloc<float>(batch * seq_len * head_dim);
    float *dO = cuda_malloc<float>(batch * seq_len * head_dim);

    cuda_memcpy_h2d(dQ, Q.data(), batch * seq_len * head_dim);
    cuda_memcpy_h2d(dK, K.data(), batch * seq_len * head_dim);
    cuda_memcpy_h2d(dV, V.data(), batch * seq_len * head_dim);

    opt78::attention_flash_v2(dO, dQ, dK, dV, batch, seq_len, head_dim);
    CHECK_KERNEL_LAUNCH();

    std::vector<float> h_output(batch * seq_len * head_dim);
    cuda_memcpy_d2h(h_output.data(), dO, batch * seq_len * head_dim);

    // Flash attention has slightly higher tolerance due to online softmax
    EXPECT_TRUE(compareVectors(ref.data(), h_output.data(), batch * seq_len * head_dim, 1e-2f))
        << "FlashAttention v2 differs from CPU reference";

    cuda_free(dQ); cuda_free(dK); cuda_free(dV); cuda_free(dO);
}

TEST_F(AttentionStagesTest, AllStagesMatch) {
    const int batch = 2, seq_len = 64, head_dim = 32;
    auto Q = randomVec(batch * seq_len * head_dim);
    auto K = randomVec(batch * seq_len * head_dim);
    auto V = randomVec(batch * seq_len * head_dim);

    int qkv_n = batch * seq_len * head_dim;
    int scores_n = batch * seq_len * seq_len;

    float *dQ = cuda_malloc<float>(qkv_n);
    float *dK = cuda_malloc<float>(qkv_n);
    float *dV = cuda_malloc<float>(qkv_n);
    float *dO_naive = cuda_malloc<float>(qkv_n);
    float *dO_tiled = cuda_malloc<float>(qkv_n);
    float *dO_flash = cuda_malloc<float>(qkv_n);
    float *dScores = cuda_malloc<float>(scores_n);

    cuda_memcpy_h2d(dQ, Q.data(), qkv_n);
    cuda_memcpy_h2d(dK, K.data(), qkv_n);
    cuda_memcpy_h2d(dV, V.data(), qkv_n);

    opt78::attention_naive(dO_naive, dScores, dQ, dK, dV, batch, seq_len, head_dim);
    opt78::attention_tiled(dO_tiled, dScores, dQ, dK, dV, batch, seq_len, head_dim);
    opt78::attention_flash_v2(dO_flash, dQ, dK, dV, batch, seq_len, head_dim);
    CHECK_KERNEL_LAUNCH();

    std::vector<float> naive(qkv_n), tiled(qkv_n), flash(qkv_n);
    cuda_memcpy_d2h(naive.data(), dO_naive, qkv_n);
    cuda_memcpy_d2h(tiled.data(), dO_tiled, qkv_n);
    cuda_memcpy_d2h(flash.data(), dO_flash, qkv_n);

    EXPECT_TRUE(compareVectors(naive.data(), tiled.data(), qkv_n))
        << "Tiled attention differs from naive";
    EXPECT_TRUE(compareVectors(naive.data(), flash.data(), qkv_n, 1e-2f))
        << "Flash v2 attention differs from naive";

    cuda_free(dQ); cuda_free(dK); cuda_free(dV);
    cuda_free(dO_naive); cuda_free(dO_tiled); cuda_free(dO_flash);
    cuda_free(dScores);
}
