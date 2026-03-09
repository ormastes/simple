/**
 * @file test_token_embedding.cu
 * @brief Unit tests for TokenEmbedding layer
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/token_embedding.h"
#include "cuda_utils.h"
#include <vector>

using namespace llm;

/**
 * @brief Test fixture for TokenEmbedding tests with GPU setup
 */
class TokenEmbeddingTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();  // Initialize GPU
    }

    void TearDown() override {
        GpuTest::TearDown();  // Cleanup GPU
    }
};

/**
 * @brief Test embedding layer construction
 */
TEST_F(TokenEmbeddingTest, Construction) {
    const int vocab_size = 1000;
    const int embed_dim = 128;

    TokenEmbedding embedding(vocab_size, embed_dim);

    EXPECT_EQ(embedding.VocabSize(), vocab_size);
    EXPECT_EQ(embedding.EmbedDim(), embed_dim);
}

/**
 * @brief Test forward pass with simple input
 */
TEST_F(TokenEmbeddingTest, Forward_SimpleInput) {
    const int vocab_size = 100;
    const int embed_dim = 64;
    const int batch_size = 2;
    const int seq_len = 5;

    TokenEmbedding embedding(vocab_size, embed_dim);

    // Create input token IDs on GPU
    std::vector<int> h_token_ids = {
        1, 2, 3, 4, 5,    // Batch 0
        10, 20, 30, 40, 50  // Batch 1
    };

    int* d_token_ids = cuda_malloc<int>(batch_size * seq_len);
    CHECK_CUDA(cudaMemcpy(d_token_ids, h_token_ids.data(),
                         h_token_ids.size() * sizeof(int),
                         cudaMemcpyHostToDevice));

    // Allocate output
    float* d_output = cuda_malloc<float>(batch_size * seq_len * embed_dim);

    // Forward pass
    embedding.Forward(d_token_ids, d_output, batch_size, seq_len);

    // Copy output to host for verification
    std::vector<float> h_output(batch_size * seq_len * embed_dim);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output,
                         h_output.size() * sizeof(float),
                         cudaMemcpyDeviceToHost));

    // Verify output shape (non-zero values)
    int non_zero_count = 0;
    for (float val : h_output) {
        if (std::abs(val) > 1e-6f) {
            non_zero_count++;
        }
    }

    // Most embeddings should be non-zero (initialized randomly)
    EXPECT_GT(non_zero_count, h_output.size() / 2);

    cuda_free(d_token_ids);
    cuda_free(d_output);
}

/**
 * @brief Test embedding lookup correctness
 */
TEST_F(TokenEmbeddingTest, Forward_LookupCorrectness) {
    const int vocab_size = 10;
    const int embed_dim = 4;

    TokenEmbedding embedding(vocab_size, embed_dim);

    // Get embedding weights
    std::vector<float> h_weights(vocab_size * embed_dim);
    embedding.GetWeights(h_weights.data());

    // Single token lookup
    const int batch_size = 1;
    const int seq_len = 1;
    const int test_token_id = 5;

    int* d_token_ids = cuda_malloc<int>(1);
    CHECK_CUDA(cudaMemcpy(d_token_ids, &test_token_id, sizeof(int),
                         cudaMemcpyHostToDevice));

    float* d_output = cuda_malloc<float>(embed_dim);

    embedding.Forward(d_token_ids, d_output, batch_size, seq_len);

    // Get output
    std::vector<float> h_output(embed_dim);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output,
                         embed_dim * sizeof(float),
                         cudaMemcpyDeviceToHost));

    // Verify matches expected embedding
    for (int i = 0; i < embed_dim; ++i) {
        float expected = h_weights[test_token_id * embed_dim + i];
        EXPECT_FLOAT_EQ(h_output[i], expected);
    }

    cuda_free(d_token_ids);
    cuda_free(d_output);
}

/**
 * @brief Test batch processing
 */
TEST_F(TokenEmbeddingTest, Forward_BatchProcessing) {
    const int vocab_size = 50;
    const int embed_dim = 32;
    const int batch_size = 8;
    const int seq_len = 16;

    TokenEmbedding embedding(vocab_size, embed_dim);

    // Random token IDs
    std::vector<int> h_token_ids(batch_size * seq_len);
    for (size_t i = 0; i < h_token_ids.size(); ++i) {
        h_token_ids[i] = i % vocab_size;
    }

    int* d_token_ids = cuda_malloc<int>(h_token_ids.size());
    CHECK_CUDA(cudaMemcpy(d_token_ids, h_token_ids.data(),
                         h_token_ids.size() * sizeof(int),
                         cudaMemcpyHostToDevice));

    float* d_output = cuda_malloc<float>(batch_size * seq_len * embed_dim);

    // Forward pass
    embedding.Forward(d_token_ids, d_output, batch_size, seq_len);

    // Verify no CUDA errors
    CHECK_CUDA(cudaDeviceSynchronize());

    cuda_free(d_token_ids);
    cuda_free(d_output);
}

/**
 * @brief Test weight loading
 */
TEST_F(TokenEmbeddingTest, LoadWeights) {
    const int vocab_size = 10;
    const int embed_dim = 4;

    TokenEmbedding embedding(vocab_size, embed_dim);

    // Create custom weights
    std::vector<float> custom_weights(vocab_size * embed_dim);
    for (size_t i = 0; i < custom_weights.size(); ++i) {
        custom_weights[i] = static_cast<float>(i);
    }

    // Load weights
    embedding.LoadWeights(custom_weights.data(), custom_weights.size());

    // Retrieve and verify
    std::vector<float> retrieved_weights(vocab_size * embed_dim);
    embedding.GetWeights(retrieved_weights.data());

    for (size_t i = 0; i < custom_weights.size(); ++i) {
        EXPECT_FLOAT_EQ(retrieved_weights[i], custom_weights[i]);
    }
}

/**
 * @brief Test large vocabulary performance
 */
TEST_F(TokenEmbeddingTest, Performance_LargeVocab) {
    const int vocab_size = 50000;  // GPT-2 vocabulary size
    const int embed_dim = 768;     // GPT-2 embedding dimension
    const int batch_size = 32;
    const int seq_len = 512;

    TokenEmbedding embedding(vocab_size, embed_dim);

    // Random token IDs
    std::vector<int> h_token_ids(batch_size * seq_len);
    for (size_t i = 0; i < h_token_ids.size(); ++i) {
        h_token_ids[i] = i % vocab_size;
    }

    int* d_token_ids = cuda_malloc<int>(h_token_ids.size());
    CHECK_CUDA(cudaMemcpy(d_token_ids, h_token_ids.data(),
                         h_token_ids.size() * sizeof(int),
                         cudaMemcpyHostToDevice));

    float* d_output = cuda_malloc<float>(batch_size * seq_len * embed_dim);

    // Warm-up
    embedding.Forward(d_token_ids, d_output, batch_size, seq_len);
    CHECK_CUDA(cudaDeviceSynchronize());

    // Time forward pass
    cudaEvent_t start, stop;
    cudaEventCreate(&start);
    cudaEventCreate(&stop);

    cudaEventRecord(start);
    for (int i = 0; i < 10; ++i) {
        embedding.Forward(d_token_ids, d_output, batch_size, seq_len);
    }
    cudaEventRecord(stop);

    cudaEventSynchronize(stop);
    float milliseconds = 0;
    cudaEventElapsedTime(&milliseconds, start, stop);

    float avg_time = milliseconds / 10.0f;
    std::cout << "Average embedding time: " << avg_time << " ms\n";
    std::cout << "Throughput: " << (batch_size * seq_len / avg_time) << "K tokens/ms\n";

    // Should be reasonably fast (< 2ms for typical GPU)
    EXPECT_LT(avg_time, 2.0f);

    cudaEventDestroy(start);
    cudaEventDestroy(stop);
    cuda_free(d_token_ids);
    cuda_free(d_output);
}

/**
 * @brief Test edge case: zero sequence length
 */
TEST_F(TokenEmbeddingTest, EdgeCase_ZeroSequenceLength) {
    const int vocab_size = 100;
    const int embed_dim = 64;

    TokenEmbedding embedding(vocab_size, embed_dim);

    int* d_token_ids = cuda_malloc<int>(1);  // Minimal allocation
    float* d_output = cuda_malloc<float>(1);

    // Forward with seq_len=0 should not crash
    embedding.Forward(d_token_ids, d_output, 1, 0);

    CHECK_CUDA(cudaDeviceSynchronize());

    cuda_free(d_token_ids);
    cuda_free(d_output);
}
