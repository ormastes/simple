/**
 * @file test_similarity.cu
 * @brief Unit tests for cosine similarity kernels
 *
 * Validates GPU cosine similarity computation against a CPU reference
 * implementation for correctness.
 */

#include <gtest/gtest.h>
#include "common/attention_similarity.h"
#include <cuda_runtime.h>
#include <cmath>
#include <vector>

/// CPU reference cosine similarity for validation
static float cpu_cosine_similarity(const float* a, const float* b, int n) {
    float dot = 0.0f, norm_a = 0.0f, norm_b = 0.0f;
    for (int i = 0; i < n; ++i) {
        dot += a[i] * b[i];
        norm_a += a[i] * a[i];
        norm_b += b[i] * b[i];
    }
    float denom = sqrtf(norm_a) * sqrtf(norm_b);
    return (denom > 1e-8f) ? (dot / denom) : 0.0f;
}

class SimilarityKernelTest : public ::testing::Test {
protected:
    static constexpr int D_MODEL = 128;
    static constexpr int NUM_EXPERTS = 8;

    float* d_hidden;
    float* d_centroids;
    float* d_similarities;

    std::vector<float> h_hidden;
    std::vector<float> h_centroids;

    void SetUp() override {
        h_hidden.resize(D_MODEL);
        h_centroids.resize(NUM_EXPERTS * D_MODEL);

        // Initialize with deterministic values
        for (int i = 0; i < D_MODEL; ++i) {
            h_hidden[i] = sinf((float)i * 0.1f);
        }
        for (int e = 0; e < NUM_EXPERTS; ++e) {
            for (int i = 0; i < D_MODEL; ++i) {
                h_centroids[e * D_MODEL + i] = cosf((float)(e * D_MODEL + i) * 0.05f);
            }
        }

        cudaMalloc(&d_hidden, D_MODEL * sizeof(float));
        cudaMalloc(&d_centroids, NUM_EXPERTS * D_MODEL * sizeof(float));
        cudaMalloc(&d_similarities, NUM_EXPERTS * sizeof(float));

        cudaMemcpy(d_hidden, h_hidden.data(), D_MODEL * sizeof(float), cudaMemcpyHostToDevice);
        cudaMemcpy(d_centroids, h_centroids.data(), NUM_EXPERTS * D_MODEL * sizeof(float), cudaMemcpyHostToDevice);
    }

    void TearDown() override {
        cudaFree(d_hidden);
        cudaFree(d_centroids);
        cudaFree(d_similarities);
    }
};

/// Test cosine similarity against CPU reference
TEST_F(SimilarityKernelTest, MatchesCpuReference) {
    llm::compute_expert_similarity(d_similarities, d_hidden, d_centroids,
                                   D_MODEL, NUM_EXPERTS);
    cudaDeviceSynchronize();

    std::vector<float> h_similarities(NUM_EXPERTS);
    cudaMemcpy(h_similarities.data(), d_similarities, NUM_EXPERTS * sizeof(float), cudaMemcpyDeviceToHost);

    for (int e = 0; e < NUM_EXPERTS; ++e) {
        float expected = cpu_cosine_similarity(h_hidden.data(),
                                               h_centroids.data() + e * D_MODEL,
                                               D_MODEL);
        EXPECT_NEAR(h_similarities[e], expected, 1e-4f)
            << "Mismatch at expert " << e;
    }
}

/// Test that similarity of identical vectors is 1.0
TEST_F(SimilarityKernelTest, IdenticalVectors) {
    // Copy hidden state as the first centroid
    cudaMemcpy(d_centroids, d_hidden, D_MODEL * sizeof(float), cudaMemcpyDeviceToDevice);

    llm::compute_expert_similarity(d_similarities, d_hidden, d_centroids,
                                   D_MODEL, 1);
    cudaDeviceSynchronize();

    float similarity;
    cudaMemcpy(&similarity, d_similarities, sizeof(float), cudaMemcpyDeviceToHost);
    EXPECT_NEAR(similarity, 1.0f, 1e-5f);
}

/// Test that similarity of orthogonal vectors is near 0
TEST_F(SimilarityKernelTest, OrthogonalVectors) {
    // Create two orthogonal vectors: [1,0,0,...] and [0,1,0,...]
    std::vector<float> h_a(D_MODEL, 0.0f);
    std::vector<float> h_b(D_MODEL, 0.0f);
    h_a[0] = 1.0f;
    h_b[1] = 1.0f;

    cudaMemcpy(d_hidden, h_a.data(), D_MODEL * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_centroids, h_b.data(), D_MODEL * sizeof(float), cudaMemcpyHostToDevice);

    llm::compute_expert_similarity(d_similarities, d_hidden, d_centroids,
                                   D_MODEL, 1);
    cudaDeviceSynchronize();

    float similarity;
    cudaMemcpy(&similarity, d_similarities, sizeof(float), cudaMemcpyDeviceToHost);
    EXPECT_NEAR(similarity, 0.0f, 1e-5f);
}

/// Test expert prediction selects highest-similarity experts
TEST_F(SimilarityKernelTest, PredictTopK) {
    llm::compute_expert_similarity(d_similarities, d_hidden, d_centroids,
                                   D_MODEL, NUM_EXPERTS);
    cudaDeviceSynchronize();

    int top_k = 2;
    int* d_predicted;
    cudaMalloc(&d_predicted, top_k * sizeof(int));

    llm::predict_experts(d_predicted, d_similarities, NUM_EXPERTS, top_k);
    cudaDeviceSynchronize();

    // Get similarities and predicted indices
    std::vector<float> h_similarities(NUM_EXPERTS);
    std::vector<int> h_predicted(top_k);
    cudaMemcpy(h_similarities.data(), d_similarities, NUM_EXPERTS * sizeof(float), cudaMemcpyDeviceToHost);
    cudaMemcpy(h_predicted.data(), d_predicted, top_k * sizeof(int), cudaMemcpyDeviceToHost);

    // Verify predicted experts are valid indices
    for (int k = 0; k < top_k; ++k) {
        EXPECT_GE(h_predicted[k], 0);
        EXPECT_LT(h_predicted[k], NUM_EXPERTS);
    }

    // Verify first predicted expert has highest similarity
    float max_sim = -1e30f;
    int max_idx = 0;
    for (int i = 0; i < NUM_EXPERTS; ++i) {
        if (h_similarities[i] > max_sim) {
            max_sim = h_similarities[i];
            max_idx = i;
        }
    }
    EXPECT_EQ(h_predicted[0], max_idx);

    cudaFree(d_predicted);
}
