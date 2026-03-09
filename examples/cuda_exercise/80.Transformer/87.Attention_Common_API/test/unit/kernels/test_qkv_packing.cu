/**
 * @file test_qkv_packing.cu
 * @brief Unit tests for QKV packing/reordering kernels
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "common/qkv_packing.cuh"
#include <vector>
#include <cmath>

using namespace transformer;

/**
 * @brief Test fixture for QKV packing tests with GPU setup
 */
class QKVPackingTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }

    /// CPU reference: reorder [B,T,H,D] -> [B,H,T,D]
    void cpu_bthd_to_bhtd(const std::vector<float>& input, std::vector<float>& output,
                           int B, int T, int H, int D) {
        output.resize(B * H * T * D);
        for (int b = 0; b < B; b++) {
            for (int t = 0; t < T; t++) {
                for (int h = 0; h < H; h++) {
                    for (int d = 0; d < D; d++) {
                        int src = b * (T * H * D) + t * (H * D) + h * D + d;
                        int dst = b * (H * T * D) + h * (T * D) + t * D + d;
                        output[dst] = input[src];
                    }
                }
            }
        }
    }

    /// CPU reference: reorder [B,H,T,D] -> [B,T,H,D]
    void cpu_bhtd_to_bthd(const std::vector<float>& input, std::vector<float>& output,
                           int B, int T, int H, int D) {
        output.resize(B * T * H * D);
        for (int b = 0; b < B; b++) {
            for (int h = 0; h < H; h++) {
                for (int t = 0; t < T; t++) {
                    for (int d = 0; d < D; d++) {
                        int src = b * (H * T * D) + h * (T * D) + t * D + d;
                        int dst = b * (T * H * D) + t * (H * D) + h * D + d;
                        output[dst] = input[src];
                    }
                }
            }
        }
    }
};

/**
 * @brief Test BTHD->BHTD reorder against CPU reference
 */
TEST_F(QKVPackingTest, BTHD_to_BHTD_MatchesCPU) {
    const int B = 2, T = 4, H = 3, D = 8;
    const int total = B * T * H * D;

    std::vector<float> h_input(total);
    for (int i = 0; i < total; i++) {
        h_input[i] = static_cast<float>(i) * 0.01f;
    }

    float* d_input = cuda_malloc<float>(total);
    float* d_output = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    reorder_bthd_to_bhtd(d_output, d_input, B, T, H, D);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total * sizeof(float), cudaMemcpyDeviceToHost));

    std::vector<float> expected;
    cpu_bthd_to_bhtd(h_input, expected, B, T, H, D);

    for (int i = 0; i < total; i++) {
        EXPECT_FLOAT_EQ(h_output[i], expected[i])
            << "Mismatch at flat index " << i;
    }

    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Test BHTD->BTHD reorder against CPU reference
 */
TEST_F(QKVPackingTest, BHTD_to_BTHD_MatchesCPU) {
    const int B = 2, T = 4, H = 3, D = 8;
    const int total = B * T * H * D;

    std::vector<float> h_input(total);
    for (int i = 0; i < total; i++) {
        h_input[i] = static_cast<float>(i) * 0.01f;
    }

    float* d_input = cuda_malloc<float>(total);
    float* d_output = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    reorder_bhtd_to_bthd(d_output, d_input, B, T, H, D);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total * sizeof(float), cudaMemcpyDeviceToHost));

    std::vector<float> expected;
    cpu_bhtd_to_bthd(h_input, expected, B, T, H, D);

    for (int i = 0; i < total; i++) {
        EXPECT_FLOAT_EQ(h_output[i], expected[i])
            << "Mismatch at flat index " << i;
    }

    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Test BTHD->BHTD->BTHD roundtrip preserves data
 */
TEST_F(QKVPackingTest, Roundtrip_BTHD_BHTD_BTHD) {
    const int B = 2, T = 8, H = 4, D = 16;
    const int total = B * T * H * D;

    std::vector<float> h_input(total);
    for (int i = 0; i < total; i++) {
        h_input[i] = sinf(static_cast<float>(i) * 0.1f);
    }

    float* d_input = cuda_malloc<float>(total);
    float* d_intermediate = cuda_malloc<float>(total);
    float* d_output = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    // Forward: BTHD -> BHTD
    reorder_bthd_to_bhtd(d_intermediate, d_input, B, T, H, D);
    // Inverse: BHTD -> BTHD
    reorder_bhtd_to_bthd(d_output, d_intermediate, B, T, H, D);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total * sizeof(float), cudaMemcpyDeviceToHost));

    for (int i = 0; i < total; i++) {
        EXPECT_FLOAT_EQ(h_output[i], h_input[i])
            << "Roundtrip mismatch at index " << i;
    }

    cuda_free(d_input);
    cuda_free(d_intermediate);
    cuda_free(d_output);
}

/**
 * @brief Test BHTD->BTHD->BHTD roundtrip preserves data
 */
TEST_F(QKVPackingTest, Roundtrip_BHTD_BTHD_BHTD) {
    const int B = 1, T = 16, H = 8, D = 64;
    const int total = B * T * H * D;

    std::vector<float> h_input(total);
    for (int i = 0; i < total; i++) {
        h_input[i] = cosf(static_cast<float>(i) * 0.05f);
    }

    float* d_input = cuda_malloc<float>(total);
    float* d_intermediate = cuda_malloc<float>(total);
    float* d_output = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    // Forward: BHTD -> BTHD
    reorder_bhtd_to_bthd(d_intermediate, d_input, B, T, H, D);
    // Inverse: BTHD -> BHTD
    reorder_bthd_to_bhtd(d_output, d_intermediate, B, T, H, D);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total * sizeof(float), cudaMemcpyDeviceToHost));

    for (int i = 0; i < total; i++) {
        EXPECT_FLOAT_EQ(h_output[i], h_input[i])
            << "Roundtrip mismatch at index " << i;
    }

    cuda_free(d_input);
    cuda_free(d_intermediate);
    cuda_free(d_output);
}

/**
 * @brief Test with B=1, T=1, H=1, D=1 (minimal case)
 */
TEST_F(QKVPackingTest, MinimalCase_B1T1H1D1) {
    const int total = 1;
    std::vector<float> h_input = {42.0f};

    float* d_input = cuda_malloc<float>(total);
    float* d_output = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), sizeof(float), cudaMemcpyHostToDevice));

    reorder_bthd_to_bhtd(d_output, d_input, 1, 1, 1, 1);
    CHECK_CUDA(cudaDeviceSynchronize());

    float h_output;
    CHECK_CUDA(cudaMemcpy(&h_output, d_output, sizeof(float), cudaMemcpyDeviceToHost));
    EXPECT_FLOAT_EQ(h_output, 42.0f);

    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Test with larger batch and sequence for typical LLM dimensions
 */
TEST_F(QKVPackingTest, TypicalLLMDimensions) {
    const int B = 4, T = 32, H = 8, D = 64;
    const int total = B * T * H * D;

    std::vector<float> h_input(total);
    for (int i = 0; i < total; i++) {
        h_input[i] = static_cast<float>(i % 1000) * 0.001f;
    }

    float* d_input = cuda_malloc<float>(total);
    float* d_intermediate = cuda_malloc<float>(total);
    float* d_output = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    reorder_bthd_to_bhtd(d_intermediate, d_input, B, T, H, D);
    reorder_bhtd_to_bthd(d_output, d_intermediate, B, T, H, D);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total * sizeof(float), cudaMemcpyDeviceToHost));

    for (int i = 0; i < total; i++) {
        EXPECT_FLOAT_EQ(h_output[i], h_input[i])
            << "Roundtrip mismatch at index " << i;
    }

    cuda_free(d_input);
    cuda_free(d_intermediate);
    cuda_free(d_output);
}

/**
 * @brief Test with H=1 (single head, should be near-identity transform)
 */
TEST_F(QKVPackingTest, SingleHead_NearIdentity) {
    const int B = 2, T = 8, H = 1, D = 16;
    const int total = B * T * H * D;

    std::vector<float> h_input(total);
    for (int i = 0; i < total; i++) {
        h_input[i] = static_cast<float>(i);
    }

    float* d_input = cuda_malloc<float>(total);
    float* d_output = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    // With H=1, BTHD and BHTD are the same layout
    reorder_bthd_to_bhtd(d_output, d_input, B, T, H, D);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total * sizeof(float), cudaMemcpyDeviceToHost));

    for (int i = 0; i < total; i++) {
        EXPECT_FLOAT_EQ(h_output[i], h_input[i])
            << "Single-head reorder should be identity, mismatch at " << i;
    }

    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Test with T=1 (single token, should be near-identity transform)
 */
TEST_F(QKVPackingTest, SingleToken_NearIdentity) {
    const int B = 2, T = 1, H = 4, D = 8;
    const int total = B * T * H * D;

    std::vector<float> h_input(total);
    for (int i = 0; i < total; i++) {
        h_input[i] = static_cast<float>(i);
    }

    float* d_input = cuda_malloc<float>(total);
    float* d_output = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    // With T=1, BTHD and BHTD are the same layout
    reorder_bthd_to_bhtd(d_output, d_input, B, T, H, D);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total * sizeof(float), cudaMemcpyDeviceToHost));

    for (int i = 0; i < total; i++) {
        EXPECT_FLOAT_EQ(h_output[i], h_input[i])
            << "Single-token reorder should be identity, mismatch at " << i;
    }

    cuda_free(d_input);
    cuda_free(d_output);
}
