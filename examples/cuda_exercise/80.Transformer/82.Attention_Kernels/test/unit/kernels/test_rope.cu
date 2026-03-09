/**
 * @file test_rope.cu
 * @brief Unit tests for Rotary Position Embeddings (RoPE)
 *
 * Validates that RoPE preserves vector norms, produces correct rotations at
 * known positions, and that position 0 is an identity operation.
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include <vector>
#include <cmath>

namespace transformer {
extern void launch_rope(float* x, int batch, int seq_len, int num_heads, int head_dim,
                        float theta_base, cudaStream_t stream);
}

/**
 * @brief Test fixture for RoPE kernel tests
 */
class RoPEKernelTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }

    /// Compute L2 norm of a vector
    float l2_norm(const float* data, int n) {
        float sum = 0.0f;
        for (int i = 0; i < n; i++) {
            sum += data[i] * data[i];
        }
        return std::sqrt(sum);
    }
};

/**
 * @brief RoPE should preserve the L2 norm of each head vector
 *
 * Rotary embeddings apply orthogonal rotations, which preserve vector norms.
 */
TEST_F(RoPEKernelTest, PreservesVectorNorm) {
    const int batch = 1;
    const int seq_len = 4;
    const int num_heads = 2;
    const int head_dim = 8;
    const float theta_base = 10000.0f;
    const int total = batch * seq_len * num_heads * head_dim;

    std::vector<float> h_input(total);
    for (int i = 0; i < total; i++) {
        h_input[i] = static_cast<float>(i + 1) * 0.1f;
    }

    // Compute norms before RoPE
    std::vector<float> norms_before;
    for (int b = 0; b < batch; b++) {
        for (int t = 0; t < seq_len; t++) {
            for (int h = 0; h < num_heads; h++) {
                int offset = b * (seq_len * num_heads * head_dim) +
                             t * (num_heads * head_dim) +
                             h * head_dim;
                norms_before.push_back(l2_norm(h_input.data() + offset, head_dim));
            }
        }
    }

    float* d_x = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_x, h_input.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    transformer::launch_rope(d_x, batch, seq_len, num_heads, head_dim, theta_base, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_x, total * sizeof(float), cudaMemcpyDeviceToHost));

    // Verify norms are preserved after RoPE
    int idx = 0;
    for (int b = 0; b < batch; b++) {
        for (int t = 0; t < seq_len; t++) {
            for (int h = 0; h < num_heads; h++) {
                int offset = b * (seq_len * num_heads * head_dim) +
                             t * (num_heads * head_dim) +
                             h * head_dim;
                float norm_after = l2_norm(h_output.data() + offset, head_dim);
                EXPECT_NEAR(norm_after, norms_before[idx], 1e-4f)
                    << "Norm changed at batch=" << b << ", pos=" << t << ", head=" << h
                    << " (before=" << norms_before[idx] << ", after=" << norm_after << ")";
                idx++;
            }
        }
    }

    cuda_free(d_x);
}

/**
 * @brief Position 0 should be identity (angle = 0, cos=1, sin=0)
 *
 * At position t=0, all rotation angles are zero, so the vector should be unchanged.
 */
TEST_F(RoPEKernelTest, Position0_IsIdentity) {
    const int batch = 1;
    const int seq_len = 1;
    const int num_heads = 2;
    const int head_dim = 8;
    const float theta_base = 10000.0f;
    const int total = batch * seq_len * num_heads * head_dim;

    std::vector<float> h_input(total);
    for (int i = 0; i < total; i++) {
        h_input[i] = static_cast<float>(i + 1) * 0.5f;
    }

    float* d_x = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_x, h_input.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    transformer::launch_rope(d_x, batch, seq_len, num_heads, head_dim, theta_base, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_x, total * sizeof(float), cudaMemcpyDeviceToHost));

    // At position 0, angle = 0 for all dims, so output should equal input
    for (int i = 0; i < total; i++) {
        EXPECT_NEAR(h_output[i], h_input[i], 1e-5f)
            << "Position 0 should be identity, mismatch at index " << i;
    }

    cuda_free(d_x);
}

/**
 * @brief Position 1 should produce actual rotations (not identity)
 *
 * At position t=1, the rotation angles are non-zero, so the output should differ
 * from the input (except for dimensions with very large theta that produce near-zero angles).
 */
TEST_F(RoPEKernelTest, Position1_ProducesRotation) {
    const int batch = 1;
    const int seq_len = 2;  // positions 0 and 1
    const int num_heads = 1;
    const int head_dim = 4;  // small for easy verification
    const float theta_base = 10000.0f;
    const int total = batch * seq_len * num_heads * head_dim;

    std::vector<float> h_input(total, 1.0f);

    float* d_x = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_x, h_input.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    transformer::launch_rope(d_x, batch, seq_len, num_heads, head_dim, theta_base, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_x, total * sizeof(float), cudaMemcpyDeviceToHost));

    // Position 0 should be unchanged
    for (int i = 0; i < head_dim; i++) {
        EXPECT_NEAR(h_output[i], h_input[i], 1e-5f);
    }

    // Position 1: verify against CPU reference
    // For dim pair (d, d+half_dim) at position t=1:
    //   freq = 1 / theta_base^(2d/head_dim)
    //   angle = 1 * freq
    //   x'[d] = cos(angle) - sin(angle)  (since both inputs are 1.0)
    //   x'[d+half] = sin(angle) + cos(angle)
    int half_dim = head_dim / 2;
    int pos1_offset = num_heads * head_dim;  // offset to position 1
    for (int d = 0; d < half_dim; d++) {
        float freq = 1.0f / std::pow(theta_base, (2.0f * d) / head_dim);
        float angle = freq;  // t=1
        float cos_val = std::cos(angle);
        float sin_val = std::sin(angle);

        float expected_d0 = cos_val - sin_val;
        float expected_d1 = sin_val + cos_val;

        EXPECT_NEAR(h_output[pos1_offset + d], expected_d0, 1e-4f)
            << "Position 1, dim " << d;
        EXPECT_NEAR(h_output[pos1_offset + d + half_dim], expected_d1, 1e-4f)
            << "Position 1, dim " << (d + half_dim);
    }

    cuda_free(d_x);
}

/**
 * @brief Multiple heads should be processed independently
 */
TEST_F(RoPEKernelTest, MultipleHeads_IndependentProcessing) {
    const int batch = 1;
    const int seq_len = 2;
    const int num_heads = 4;
    const int head_dim = 8;
    const float theta_base = 10000.0f;
    const int total = batch * seq_len * num_heads * head_dim;

    // Set all heads to the same values
    std::vector<float> h_input(total);
    for (int t = 0; t < seq_len; t++) {
        for (int h = 0; h < num_heads; h++) {
            for (int d = 0; d < head_dim; d++) {
                h_input[t * num_heads * head_dim + h * head_dim + d] =
                    static_cast<float>(d + 1) * 0.1f;
            }
        }
    }

    float* d_x = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_x, h_input.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    transformer::launch_rope(d_x, batch, seq_len, num_heads, head_dim, theta_base, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_x, total * sizeof(float), cudaMemcpyDeviceToHost));

    // All heads at the same position should produce the same output
    // (since they had the same input values)
    for (int t = 0; t < seq_len; t++) {
        for (int h = 1; h < num_heads; h++) {
            for (int d = 0; d < head_dim; d++) {
                int idx_h0 = t * num_heads * head_dim + 0 * head_dim + d;
                int idx_h = t * num_heads * head_dim + h * head_dim + d;
                EXPECT_NEAR(h_output[idx_h], h_output[idx_h0], 1e-5f)
                    << "Heads should produce same output for same input at pos="
                    << t << ", head=" << h << ", dim=" << d;
            }
        }
    }

    cuda_free(d_x);
}
