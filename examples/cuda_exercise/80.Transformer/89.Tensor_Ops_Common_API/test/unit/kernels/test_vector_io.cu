/**
 * @file test_vector_io.cu
 * @brief Unit tests for vectorized load/store operations
 *
 * Tests float4, float2, half2 load/store roundtrips, alignment checking,
 * safe_load_float4 for aligned and unaligned addresses, and vectorized_copy.
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/vector_io.cuh"

// ---------------------------------------------------------------------------
// Test kernels
// ---------------------------------------------------------------------------

/**
 * @brief Kernel: float4 load/store roundtrip
 *
 * Loads 4 floats via load_float4, stores via store_float4, verifies contents.
 */
__global__ void kernel_test_float4_roundtrip(const float* src, float* dst,
                                              int* pass_flag) {
    float4 v = transformer::load_float4(src);
    transformer::store_float4(dst, v);

    // Verify on device
    if (dst[0] == src[0] && dst[1] == src[1] &&
        dst[2] == src[2] && dst[3] == src[3]) {
        atomicExch(pass_flag, 1);
    }
}

/**
 * @brief Kernel: float2 load/store roundtrip
 */
__global__ void kernel_test_float2_roundtrip(const float* src, float* dst,
                                              int* pass_flag) {
    float2 v = transformer::load_float2(src);
    transformer::store_float2(dst, v);

    if (dst[0] == src[0] && dst[1] == src[1]) {
        atomicExch(pass_flag, 1);
    }
}

/**
 * @brief Kernel: half2 load/store roundtrip
 */
__global__ void kernel_test_half2_roundtrip(const half* src, half* dst,
                                             int* pass_flag) {
    half2 v = transformer::load_half2(src);
    transformer::store_half2(dst, v);

    if (__heq(dst[0], src[0]) && __heq(dst[1], src[1])) {
        atomicExch(pass_flag, 1);
    }
}

/**
 * @brief Kernel: alignment check
 */
__global__ void kernel_test_alignment(const float* aligned_ptr,
                                       const float* unaligned_ptr,
                                       int* results) {
    // results[0] = is_aligned<16>(aligned_ptr)
    // results[1] = is_aligned<16>(unaligned_ptr)
    // results[2] = is_aligned<4>(unaligned_ptr)
    results[0] = transformer::is_aligned<16>(aligned_ptr) ? 1 : 0;
    results[1] = transformer::is_aligned<16>(unaligned_ptr) ? 1 : 0;
    results[2] = transformer::is_aligned<4>(unaligned_ptr) ? 1 : 0;
}

/**
 * @brief Kernel: safe_load_float4 with aligned input
 */
__global__ void kernel_test_safe_load_aligned(const float* src, float* dst,
                                               int* pass_flag) {
    float buf[4];
    transformer::safe_load_float4(buf, src);
    for (int i = 0; i < 4; i++) {
        dst[i] = buf[i];
    }
    if (dst[0] == src[0] && dst[1] == src[1] &&
        dst[2] == src[2] && dst[3] == src[3]) {
        atomicExch(pass_flag, 1);
    }
}

/**
 * @brief Kernel: safe_load_float4 with unaligned input (offset by 1 float)
 */
__global__ void kernel_test_safe_load_unaligned(const float* src, float* dst,
                                                 int* pass_flag) {
    // src+1 is 4-byte aligned but not 16-byte aligned
    float buf[4];
    transformer::safe_load_float4(buf, src + 1);
    for (int i = 0; i < 4; i++) {
        dst[i] = buf[i];
    }
    if (dst[0] == src[1] && dst[1] == src[2] &&
        dst[2] == src[3] && dst[3] == src[4]) {
        atomicExch(pass_flag, 1);
    }
}

/**
 * @brief Kernel: vectorized_copy for a range of elements
 */
__global__ void kernel_test_vectorized_copy(const float* src, float* dst,
                                             int n, int* pass_flag) {
    transformer::vectorized_copy<4>(dst, src, n);

    // Verify all elements
    bool ok = true;
    for (int i = 0; i < n; i++) {
        if (dst[i] != src[i]) {
            ok = false;
            break;
        }
    }
    if (ok) {
        atomicExch(pass_flag, 1);
    }
}

// ---------------------------------------------------------------------------
// Test fixture
// ---------------------------------------------------------------------------

class VectorIOTest : public GpuTest {
protected:
    static constexpr int N = 64;

    float* d_src = nullptr;
    float* d_dst = nullptr;
    int* d_flag = nullptr;

    float h_src[N];
    float h_dst[N];

    void SetUp() override {
        GpuTest::SetUp();

        for (int i = 0; i < N; i++) {
            h_src[i] = static_cast<float>(i + 1);
            h_dst[i] = 0.0f;
        }

        cudaMalloc(&d_src, N * sizeof(float));
        cudaMalloc(&d_dst, N * sizeof(float));
        cudaMalloc(&d_flag, sizeof(int));

        cudaMemcpy(d_src, h_src, N * sizeof(float), cudaMemcpyHostToDevice);
        cudaMemset(d_dst, 0, N * sizeof(float));
        cudaMemset(d_flag, 0, sizeof(int));
    }

    void TearDown() override {
        cudaFree(d_src);
        cudaFree(d_dst);
        cudaFree(d_flag);
        GpuTest::TearDown();
    }

    bool check_pass_flag() {
        int h_flag = 0;
        cudaMemcpy(&h_flag, d_flag, sizeof(int), cudaMemcpyDeviceToHost);
        return h_flag == 1;
    }
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

TEST_F(VectorIOTest, Float4LoadStoreRoundtrip) {
    kernel_test_float4_roundtrip<<<1, 1>>>(d_src, d_dst, d_flag);
    cudaDeviceSynchronize();

    ASSERT_TRUE(check_pass_flag());

    cudaMemcpy(h_dst, d_dst, 4 * sizeof(float), cudaMemcpyDeviceToHost);
    for (int i = 0; i < 4; i++) {
        EXPECT_FLOAT_EQ(h_dst[i], h_src[i]);
    }
}

TEST_F(VectorIOTest, Float2LoadStoreRoundtrip) {
    kernel_test_float2_roundtrip<<<1, 1>>>(d_src, d_dst, d_flag);
    cudaDeviceSynchronize();

    ASSERT_TRUE(check_pass_flag());

    cudaMemcpy(h_dst, d_dst, 2 * sizeof(float), cudaMemcpyDeviceToHost);
    for (int i = 0; i < 2; i++) {
        EXPECT_FLOAT_EQ(h_dst[i], h_src[i]);
    }
}

TEST_F(VectorIOTest, Half2LoadStoreRoundtrip) {
    half h_half_src[2] = {__float2half(1.0f), __float2half(2.0f)};
    half h_half_dst[2] = {__float2half(0.0f), __float2half(0.0f)};

    half* d_half_src = nullptr;
    half* d_half_dst = nullptr;
    cudaMalloc(&d_half_src, 2 * sizeof(half));
    cudaMalloc(&d_half_dst, 2 * sizeof(half));
    cudaMemcpy(d_half_src, h_half_src, 2 * sizeof(half), cudaMemcpyHostToDevice);
    cudaMemset(d_half_dst, 0, 2 * sizeof(half));
    cudaMemset(d_flag, 0, sizeof(int));

    kernel_test_half2_roundtrip<<<1, 1>>>(d_half_src, d_half_dst, d_flag);
    cudaDeviceSynchronize();

    ASSERT_TRUE(check_pass_flag());

    cudaMemcpy(h_half_dst, d_half_dst, 2 * sizeof(half), cudaMemcpyDeviceToHost);
    EXPECT_FLOAT_EQ(__half2float(h_half_dst[0]), 1.0f);
    EXPECT_FLOAT_EQ(__half2float(h_half_dst[1]), 2.0f);

    cudaFree(d_half_src);
    cudaFree(d_half_dst);
}

TEST_F(VectorIOTest, AlignmentCheck) {
    // d_src from cudaMalloc is guaranteed 256-byte aligned
    int h_results[3] = {0, 0, 0};
    int* d_results = nullptr;
    cudaMalloc(&d_results, 3 * sizeof(int));
    cudaMemset(d_results, 0, 3 * sizeof(int));

    // d_src is aligned, d_src+1 is offset by 4 bytes (not 16-byte aligned)
    kernel_test_alignment<<<1, 1>>>(d_src, d_src + 1, d_results);
    cudaDeviceSynchronize();

    cudaMemcpy(h_results, d_results, 3 * sizeof(int), cudaMemcpyDeviceToHost);

    EXPECT_EQ(h_results[0], 1) << "cudaMalloc pointer should be 16-byte aligned";
    EXPECT_EQ(h_results[1], 0) << "ptr+1 (4-byte offset) should NOT be 16-byte aligned";
    EXPECT_EQ(h_results[2], 1) << "ptr+1 should still be 4-byte aligned";

    cudaFree(d_results);
}

TEST_F(VectorIOTest, SafeLoadFloat4Aligned) {
    kernel_test_safe_load_aligned<<<1, 1>>>(d_src, d_dst, d_flag);
    cudaDeviceSynchronize();

    ASSERT_TRUE(check_pass_flag());

    cudaMemcpy(h_dst, d_dst, 4 * sizeof(float), cudaMemcpyDeviceToHost);
    for (int i = 0; i < 4; i++) {
        EXPECT_FLOAT_EQ(h_dst[i], h_src[i]);
    }
}

TEST_F(VectorIOTest, SafeLoadFloat4Unaligned) {
    // Need at least 5 source elements (src[1..4])
    kernel_test_safe_load_unaligned<<<1, 1>>>(d_src, d_dst, d_flag);
    cudaDeviceSynchronize();

    ASSERT_TRUE(check_pass_flag());

    cudaMemcpy(h_dst, d_dst, 4 * sizeof(float), cudaMemcpyDeviceToHost);
    for (int i = 0; i < 4; i++) {
        EXPECT_FLOAT_EQ(h_dst[i], h_src[i + 1]);
    }
}

TEST_F(VectorIOTest, VectorizedCopyExactMultipleOf4) {
    const int count = 16;
    kernel_test_vectorized_copy<<<1, 1>>>(d_src, d_dst, count, d_flag);
    cudaDeviceSynchronize();

    ASSERT_TRUE(check_pass_flag());

    cudaMemcpy(h_dst, d_dst, count * sizeof(float), cudaMemcpyDeviceToHost);
    for (int i = 0; i < count; i++) {
        EXPECT_FLOAT_EQ(h_dst[i], h_src[i]);
    }
}

TEST_F(VectorIOTest, VectorizedCopyNonMultipleOf4) {
    const int count = 7;
    cudaMemset(d_flag, 0, sizeof(int));
    kernel_test_vectorized_copy<<<1, 1>>>(d_src, d_dst, count, d_flag);
    cudaDeviceSynchronize();

    ASSERT_TRUE(check_pass_flag());

    cudaMemcpy(h_dst, d_dst, count * sizeof(float), cudaMemcpyDeviceToHost);
    for (int i = 0; i < count; i++) {
        EXPECT_FLOAT_EQ(h_dst[i], h_src[i]);
    }
}

TEST_F(VectorIOTest, VectorizedCopySingleElement) {
    const int count = 1;
    cudaMemset(d_flag, 0, sizeof(int));
    kernel_test_vectorized_copy<<<1, 1>>>(d_src, d_dst, count, d_flag);
    cudaDeviceSynchronize();

    ASSERT_TRUE(check_pass_flag());

    cudaMemcpy(h_dst, d_dst, count * sizeof(float), cudaMemcpyDeviceToHost);
    EXPECT_FLOAT_EQ(h_dst[0], h_src[0]);
}
