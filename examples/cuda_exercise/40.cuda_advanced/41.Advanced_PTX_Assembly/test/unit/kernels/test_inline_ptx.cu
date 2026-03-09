#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "kernels/inline_ptx.cu"

class InlinePTXTest : public GpuTest {};

// Test basic addition using PTX
TEST_F(InlinePTXTest, AddOperationWorks) {
    int* d_result = cuda_malloc<int>(1);

    test_add_kernel<<<1, 1>>>(d_result, 42, 17);
    CHECK_KERNEL_LAUNCH();

    int h_result;
    cudaMemcpy(&h_result, d_result, sizeof(int), cudaMemcpyDeviceToHost);

    EXPECT_EQ(h_result, 59);
    cudaFree(d_result);
}

// Test population count
TEST_F(InlinePTXTest, PopulationCountWorks) {
    int* d_result = cuda_malloc<int>(1);

    test_popc_kernel<<<1, 1>>>(d_result, 0xF0F0F0F0);
    CHECK_KERNEL_LAUNCH();

    int h_result;
    cudaMemcpy(&h_result, d_result, sizeof(int), cudaMemcpyDeviceToHost);

    EXPECT_EQ(h_result, 16);  // 16 bits set in 0xF0F0F0F0
    cudaFree(d_result);
}

// Test bit reversal
TEST_F(InlinePTXTest, ReverseBitsWorks) {
    int* d_result = cuda_malloc<int>(1);

    test_reverse_bits_kernel<<<1, 1>>>(d_result, 0x00000001);
    CHECK_KERNEL_LAUNCH();

    int h_result;
    cudaMemcpy(&h_result, d_result, sizeof(int), cudaMemcpyDeviceToHost);

    EXPECT_EQ((unsigned int)h_result, 0x80000000u);
    cudaFree(d_result);
}

// Test FMA operation
TEST_F(InlinePTXTest, FMAWorks) {
    float* d_result = cuda_malloc<float>(1);

    test_fma_kernel<<<1, 1>>>(d_result, 2.0f, 3.0f, 1.5f);
    CHECK_KERNEL_LAUNCH();

    float h_result;
    cudaMemcpy(&h_result, d_result, sizeof(float), cudaMemcpyDeviceToHost);

    EXPECT_FLOAT_EQ(h_result, 7.5f);  // 2.0 * 3.0 + 1.5 = 7.5
    cudaFree(d_result);
}

TEST_F(InlinePTXTest, PlaceholderTest) {
    EXPECT_TRUE(true);
}
