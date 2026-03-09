/**
 * @file test_causal_mask.cu
 * @brief Unit tests for causal masking predicates
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "common/causal_mask.cuh"
#include <vector>
#include <cfloat>

using namespace transformer;

/**
 * @brief Test fixture for causal mask tests with GPU setup
 */
class CausalMaskTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }
};

/**
 * @brief Kernel to test causal_keep predicate for a full NxN matrix
 */
__global__ void kernel_causal_keep_matrix(bool* __restrict__ output, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= N * N) return;
    int q = idx / N;
    int k = idx % N;
    output[idx] = causal_keep(q, k);
}

/**
 * @brief Kernel to test apply_causal_mask for a full NxN matrix
 */
__global__ void kernel_apply_causal_mask_matrix(float* __restrict__ output,
                                                 const float* __restrict__ scores,
                                                 int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= N * N) return;
    int q = idx / N;
    int k = idx % N;
    output[idx] = apply_causal_mask(scores[idx], q, k);
}

/**
 * @brief Kernel to test tile_causal_keep for a tile
 */
__global__ void kernel_tile_causal_keep(bool* __restrict__ output,
                                         int q_start, int k_start,
                                         int q_size, int k_size) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= q_size * k_size) return;
    int q_offset = idx / k_size;
    int k_offset = idx % k_size;
    output[idx] = tile_causal_keep(q_start, k_start, q_offset, k_offset);
}

/**
 * @brief Kernel to test tile_fully_masked
 */
__global__ void kernel_tile_fully_masked(bool* __restrict__ output,
                                          int q_start, int q_size, int k_start) {
    *output = tile_fully_masked(q_start, q_size, k_start);
}

/**
 * @brief Kernel to test tile_fully_unmasked
 */
__global__ void kernel_tile_fully_unmasked(bool* __restrict__ output,
                                            int q_start, int k_start, int k_size) {
    *output = tile_fully_unmasked(q_start, k_start, k_size);
}

/**
 * @brief Test causal_keep produces correct lower-triangular pattern
 */
TEST_F(CausalMaskTest, CausalKeep_LowerTriangular) {
    const int N = 8;
    const int total = N * N;

    bool* d_output = cuda_malloc<bool>(total);
    kernel_causal_keep_matrix<<<(total + 255) / 256, 256>>>(d_output, N);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<char> h_output_raw(total);
    CHECK_CUDA(cudaMemcpy(h_output_raw.data(), d_output, total * sizeof(bool), cudaMemcpyDeviceToHost));

    for (int q = 0; q < N; q++) {
        for (int k = 0; k < N; k++) {
            bool expected = (k <= q);
            EXPECT_EQ(static_cast<bool>(h_output_raw[q * N + k]), expected)
                << "Mismatch at q=" << q << ", k=" << k;
        }
    }

    cuda_free(d_output);
}

/**
 * @brief Test apply_causal_mask preserves scores on diagonal and below
 */
TEST_F(CausalMaskTest, ApplyCausalMask_PreservesLowerTriangle) {
    const int N = 8;
    const int total = N * N;

    std::vector<float> h_scores(total);
    for (int i = 0; i < total; i++) {
        h_scores[i] = static_cast<float>(i) * 0.1f;
    }

    float* d_scores = cuda_malloc<float>(total);
    float* d_output = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_scores, h_scores.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    kernel_apply_causal_mask_matrix<<<(total + 255) / 256, 256>>>(d_output, d_scores, N);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total * sizeof(float), cudaMemcpyDeviceToHost));

    for (int q = 0; q < N; q++) {
        for (int k = 0; k < N; k++) {
            int idx = q * N + k;
            if (k <= q) {
                EXPECT_FLOAT_EQ(h_output[idx], h_scores[idx])
                    << "Score should be preserved at q=" << q << ", k=" << k;
            } else {
                EXPECT_EQ(h_output[idx], -FLT_MAX)
                    << "Score should be -inf at q=" << q << ", k=" << k;
            }
        }
    }

    cuda_free(d_scores);
    cuda_free(d_output);
}

/**
 * @brief Test tile_causal_keep with offset tile positions
 */
TEST_F(CausalMaskTest, TileCausalKeep_OffsetTile) {
    const int q_start = 4;
    const int k_start = 2;
    const int q_size = 4;
    const int k_size = 4;
    const int total = q_size * k_size;

    bool* d_output = cuda_malloc<bool>(total);
    kernel_tile_causal_keep<<<1, total>>>(d_output, q_start, k_start, q_size, k_size);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<char> h_output_raw(total);
    CHECK_CUDA(cudaMemcpy(h_output_raw.data(), d_output, total * sizeof(bool), cudaMemcpyDeviceToHost));

    for (int qo = 0; qo < q_size; qo++) {
        for (int ko = 0; ko < k_size; ko++) {
            bool expected = (k_start + ko) <= (q_start + qo);
            EXPECT_EQ(static_cast<bool>(h_output_raw[qo * k_size + ko]), expected)
                << "Mismatch at q_offset=" << qo << ", k_offset=" << ko
                << " (global q=" << (q_start + qo) << ", k=" << (k_start + ko) << ")";
        }
    }

    cuda_free(d_output);
}

/**
 * @brief Test tile_fully_masked when key tile is entirely above the diagonal
 */
TEST_F(CausalMaskTest, TileFullyMasked_True) {
    // q_start=0, q_size=4, k_start=5 => q_end=3 < k_start=5 => fully masked
    bool* d_output = cuda_malloc<bool>(1);
    kernel_tile_fully_masked<<<1, 1>>>(d_output, 0, 4, 5);
    CHECK_CUDA(cudaDeviceSynchronize());

    bool h_result;
    CHECK_CUDA(cudaMemcpy(&h_result, d_output, sizeof(bool), cudaMemcpyDeviceToHost));
    EXPECT_TRUE(h_result);

    cuda_free(d_output);
}

/**
 * @brief Test tile_fully_masked when tile overlaps the diagonal
 */
TEST_F(CausalMaskTest, TileFullyMasked_False) {
    // q_start=4, q_size=4, k_start=5 => q_end=7 >= k_start=5 => NOT fully masked
    bool* d_output = cuda_malloc<bool>(1);
    kernel_tile_fully_masked<<<1, 1>>>(d_output, 4, 4, 5);
    CHECK_CUDA(cudaDeviceSynchronize());

    bool h_result;
    CHECK_CUDA(cudaMemcpy(&h_result, d_output, sizeof(bool), cudaMemcpyDeviceToHost));
    EXPECT_FALSE(h_result);

    cuda_free(d_output);
}

/**
 * @brief Test tile_fully_unmasked when key tile is entirely below the diagonal
 */
TEST_F(CausalMaskTest, TileFullyUnmasked_True) {
    // q_start=8, k_start=0, k_size=4 => k_end=3, q_start=8 >= 3 => fully unmasked
    bool* d_output = cuda_malloc<bool>(1);
    kernel_tile_fully_unmasked<<<1, 1>>>(d_output, 8, 0, 4);
    CHECK_CUDA(cudaDeviceSynchronize());

    bool h_result;
    CHECK_CUDA(cudaMemcpy(&h_result, d_output, sizeof(bool), cudaMemcpyDeviceToHost));
    EXPECT_TRUE(h_result);

    cuda_free(d_output);
}

/**
 * @brief Test tile_fully_unmasked when tile overlaps the diagonal
 */
TEST_F(CausalMaskTest, TileFullyUnmasked_False) {
    // q_start=2, k_start=0, k_size=4 => k_end=3, q_start=2 < 3 => NOT fully unmasked
    bool* d_output = cuda_malloc<bool>(1);
    kernel_tile_fully_unmasked<<<1, 1>>>(d_output, 2, 0, 4);
    CHECK_CUDA(cudaDeviceSynchronize());

    bool h_result;
    CHECK_CUDA(cudaMemcpy(&h_result, d_output, sizeof(bool), cudaMemcpyDeviceToHost));
    EXPECT_FALSE(h_result);

    cuda_free(d_output);
}

/**
 * @brief Test diagonal tile: partially masked and partially unmasked
 */
TEST_F(CausalMaskTest, DiagonalTile_PartialMask) {
    // Tile on the diagonal: q_start=4, k_start=4, size=4x4
    // Should have: fully_masked=false, fully_unmasked=false
    bool* d_masked = cuda_malloc<bool>(1);
    bool* d_unmasked = cuda_malloc<bool>(1);

    kernel_tile_fully_masked<<<1, 1>>>(d_masked, 4, 4, 4);
    kernel_tile_fully_unmasked<<<1, 1>>>(d_unmasked, 4, 4, 4);
    CHECK_CUDA(cudaDeviceSynchronize());

    bool h_masked, h_unmasked;
    CHECK_CUDA(cudaMemcpy(&h_masked, d_masked, sizeof(bool), cudaMemcpyDeviceToHost));
    CHECK_CUDA(cudaMemcpy(&h_unmasked, d_unmasked, sizeof(bool), cudaMemcpyDeviceToHost));

    EXPECT_FALSE(h_masked) << "Diagonal tile should not be fully masked";
    EXPECT_FALSE(h_unmasked) << "Diagonal tile should not be fully unmasked";

    cuda_free(d_masked);
    cuda_free(d_unmasked);
}

/**
 * @brief Test single-element edge cases
 */
TEST_F(CausalMaskTest, SingleElement_EdgeCases) {
    const int total = 1;

    // Single element at (0,0) should be unmasked
    bool* d_output = cuda_malloc<bool>(total);
    kernel_causal_keep_matrix<<<1, 1>>>(d_output, 1);
    CHECK_CUDA(cudaDeviceSynchronize());

    bool h_result;
    CHECK_CUDA(cudaMemcpy(&h_result, d_output, sizeof(bool), cudaMemcpyDeviceToHost));
    EXPECT_TRUE(h_result) << "Position (0,0) should be unmasked";

    cuda_free(d_output);
}
