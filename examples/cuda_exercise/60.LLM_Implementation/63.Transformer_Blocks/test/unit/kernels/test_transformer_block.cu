/**
 * @file test_transformer_block.cu
 * @brief Unit tests for the complete transformer block
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/transformer_block.h"
#include "cuda_utils.h"
#include <vector>
#include <cmath>

using namespace llm;

/**
 * @brief Test fixture for TransformerBlock tests with GPU setup
 */
class TransformerBlockTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }
};

/**
 * @brief Test transformer block weight allocation (LayerNorm variant)
 */
TEST_F(TransformerBlockTest, WeightAllocation_LayerNorm) {
    TransformerBlockConfig config(64, 4, 256, 128, 0.0f, false);

    TransformerBlockWeights weights = allocate_transformer_block_weights(config);

    // Verify attention weights are allocated
    EXPECT_NE(weights.attn.W_Q, nullptr);
    EXPECT_NE(weights.attn.W_K, nullptr);
    EXPECT_NE(weights.attn.W_V, nullptr);
    EXPECT_NE(weights.attn.W_O, nullptr);

    // Verify FFN weights are allocated
    EXPECT_NE(weights.ffn.W1, nullptr);
    EXPECT_NE(weights.ffn.W2, nullptr);

    // Verify LayerNorm weights are allocated
    EXPECT_NE(weights.norm1.gamma, nullptr);
    EXPECT_NE(weights.norm1.beta, nullptr);
    EXPECT_NE(weights.norm2.gamma, nullptr);
    EXPECT_NE(weights.norm2.beta, nullptr);

    // RMSNorm weights should be null
    EXPECT_EQ(weights.rms_weight1, nullptr);
    EXPECT_EQ(weights.rms_weight2, nullptr);

    free_transformer_block_weights(weights, config);
}

/**
 * @brief Test transformer block weight allocation (RMSNorm variant)
 */
TEST_F(TransformerBlockTest, WeightAllocation_RMSNorm) {
    TransformerBlockConfig config(64, 4, 256, 128, 0.0f, true);

    TransformerBlockWeights weights = allocate_transformer_block_weights(config);

    // Verify RMSNorm weights are allocated
    EXPECT_NE(weights.rms_weight1, nullptr);
    EXPECT_NE(weights.rms_weight2, nullptr);

    // LayerNorm weights should be null
    EXPECT_EQ(weights.norm1.gamma, nullptr);
    EXPECT_EQ(weights.norm1.beta, nullptr);

    free_transformer_block_weights(weights, config);
}

/**
 * @brief Test forward pass produces correct output shape
 *
 * Output should have the same shape as input: [batch, seq, d_model]
 */
TEST_F(TransformerBlockTest, ForwardShape) {
    const int batch_size = 2;
    const int seq_len = 4;
    const int d_model = 32;
    const int num_heads = 4;

    TransformerBlockConfig config(d_model, num_heads);
    TransformerBlockWeights weights = allocate_transformer_block_weights(config);

    int total_elements = batch_size * seq_len * d_model;

    // Create input
    std::vector<float> h_input(total_elements);
    for (size_t i = 0; i < h_input.size(); ++i) {
        h_input[i] = static_cast<float>(i % 11) * 0.1f - 0.5f;
    }

    float* d_input = cuda_malloc<float>(total_elements);
    float* d_output = cuda_malloc<float>(total_elements);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(),
                          total_elements * sizeof(float), cudaMemcpyHostToDevice));

    // Forward pass
    transformer_block_forward(d_output, d_input, weights, config,
                             batch_size, seq_len);
    CHECK_CUDA(cudaDeviceSynchronize());

    // Copy output and verify all values are finite
    std::vector<float> h_output(total_elements);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output,
                          total_elements * sizeof(float), cudaMemcpyDeviceToHost));

    for (size_t i = 0; i < h_output.size(); ++i) {
        EXPECT_TRUE(std::isfinite(h_output[i]))
            << "Non-finite value at index " << i << ": " << h_output[i];
    }

    free_transformer_block_weights(weights, config);
    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Test residual connection: output should differ from input
 *
 * Due to the residual connection, the output should be related to but
 * different from the input (input + transformation != input in general).
 */
TEST_F(TransformerBlockTest, ResidualConnection) {
    const int batch_size = 1;
    const int seq_len = 4;
    const int d_model = 32;
    const int num_heads = 4;

    TransformerBlockConfig config(d_model, num_heads);
    TransformerBlockWeights weights = allocate_transformer_block_weights(config);

    int total_elements = batch_size * seq_len * d_model;

    // Create non-zero input
    std::vector<float> h_input(total_elements);
    for (size_t i = 0; i < h_input.size(); ++i) {
        h_input[i] = static_cast<float>(i % 5) * 0.3f + 0.1f;
    }

    float* d_input = cuda_malloc<float>(total_elements);
    float* d_output = cuda_malloc<float>(total_elements);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(),
                          total_elements * sizeof(float), cudaMemcpyHostToDevice));

    transformer_block_forward(d_output, d_input, weights, config,
                             batch_size, seq_len);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total_elements);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output,
                          total_elements * sizeof(float), cudaMemcpyDeviceToHost));

    // Output should differ from input (non-zero transformation)
    int differ_count = 0;
    for (size_t i = 0; i < h_output.size(); ++i) {
        if (std::abs(h_output[i] - h_input[i]) > 1e-6f) {
            differ_count++;
        }
    }
    EXPECT_GT(differ_count, 0) << "Output is identical to input; residual not working";

    free_transformer_block_weights(weights, config);
    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Test transformer block with RMSNorm variant
 */
TEST_F(TransformerBlockTest, RMSNormVariant) {
    const int batch_size = 2;
    const int seq_len = 4;
    const int d_model = 32;
    const int num_heads = 4;

    TransformerBlockConfig config(d_model, num_heads, 0, 1024, 0.0f, true);
    TransformerBlockWeights weights = allocate_transformer_block_weights(config);

    int total_elements = batch_size * seq_len * d_model;

    std::vector<float> h_input(total_elements);
    for (size_t i = 0; i < h_input.size(); ++i) {
        h_input[i] = static_cast<float>(i % 9) * 0.2f - 0.8f;
    }

    float* d_input = cuda_malloc<float>(total_elements);
    float* d_output = cuda_malloc<float>(total_elements);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(),
                          total_elements * sizeof(float), cudaMemcpyHostToDevice));

    transformer_block_forward(d_output, d_input, weights, config,
                             batch_size, seq_len);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total_elements);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output,
                          total_elements * sizeof(float), cudaMemcpyDeviceToHost));

    // Verify output is finite
    for (size_t i = 0; i < h_output.size(); ++i) {
        EXPECT_TRUE(std::isfinite(h_output[i]))
            << "Non-finite value at index " << i;
    }

    free_transformer_block_weights(weights, config);
    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Test vector_add kernel directly
 */
TEST_F(TransformerBlockTest, VectorAdd) {
    const int size = 256;

    std::vector<float> h_a(size);
    std::vector<float> h_b(size);
    for (int i = 0; i < size; ++i) {
        h_a[i] = static_cast<float>(i);
        h_b[i] = static_cast<float>(i) * 2.0f;
    }

    float* d_a = cuda_malloc<float>(size);
    float* d_b = cuda_malloc<float>(size);
    float* d_out = cuda_malloc<float>(size);
    CHECK_CUDA(cudaMemcpy(d_a, h_a.data(), size * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_b, h_b.data(), size * sizeof(float), cudaMemcpyHostToDevice));

    int block_size = 256;
    int grid_size = (size + block_size - 1) / block_size;
    vector_add_kernel<<<grid_size, block_size>>>(d_out, d_a, d_b, size);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_out(size);
    CHECK_CUDA(cudaMemcpy(h_out.data(), d_out, size * sizeof(float), cudaMemcpyDeviceToHost));

    for (int i = 0; i < size; ++i) {
        EXPECT_FLOAT_EQ(h_out[i], h_a[i] + h_b[i])
            << "Vector add mismatch at index " << i;
    }

    cuda_free(d_a);
    cuda_free(d_b);
    cuda_free(d_out);
}

/**
 * @brief Test default FFN dimension in config
 */
TEST_F(TransformerBlockTest, DefaultConfig) {
    TransformerBlockConfig config(128, 8);

    EXPECT_EQ(config.d_model, 128);
    EXPECT_EQ(config.num_heads, 8);
    EXPECT_EQ(config.d_ff, 4 * 128);
    EXPECT_EQ(config.max_seq_len, 1024);
    EXPECT_FLOAT_EQ(config.dropout, 0.0f);
    EXPECT_FALSE(config.use_rms_norm);
}

/**
 * @brief Test free sets all weight pointers to null
 */
TEST_F(TransformerBlockTest, FreeWeights) {
    TransformerBlockConfig config(32, 4);
    TransformerBlockWeights weights = allocate_transformer_block_weights(config);

    free_transformer_block_weights(weights, config);

    EXPECT_EQ(weights.attn.W_Q, nullptr);
    EXPECT_EQ(weights.attn.W_K, nullptr);
    EXPECT_EQ(weights.attn.W_V, nullptr);
    EXPECT_EQ(weights.attn.W_O, nullptr);
    EXPECT_EQ(weights.ffn.W1, nullptr);
    EXPECT_EQ(weights.ffn.W2, nullptr);
    EXPECT_EQ(weights.norm1.gamma, nullptr);
    EXPECT_EQ(weights.norm2.gamma, nullptr);
}
