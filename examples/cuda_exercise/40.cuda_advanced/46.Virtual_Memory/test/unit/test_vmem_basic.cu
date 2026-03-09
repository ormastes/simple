// test_vmem_basic.cu - Tests for basic virtual memory concepts

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "host/vmem_basics.cpp"
#include "kernels/vmem_kernel.cu"

class VMemBasicTest : public GpuTest {};

TEST_F(VMemBasicTest, InitVirtualMemoryWorks) {
    SimplifiedVirtualMemory vmem;
    const size_t requestedSize = 1024 * sizeof(int);

    ASSERT_TRUE(initVirtualMemory(&vmem, requestedSize));
    EXPECT_NE(getVirtualPtr(&vmem), nullptr);
    EXPECT_GE(getVirtualSize(&vmem), requestedSize);
    EXPECT_GT(getGranularity(&vmem), 0);

    freeVirtualMemory(&vmem);
}

TEST_F(VMemBasicTest, VirtualMemoryAlignmentCorrect) {
    SimplifiedVirtualMemory vmem;
    const size_t requestedSize = 1234;  // Odd size

    ASSERT_TRUE(initVirtualMemory(&vmem, requestedSize));

    size_t actualSize = getVirtualSize(&vmem);
    size_t granularity = getGranularity(&vmem);

    // Size should be aligned to granularity
    EXPECT_EQ(actualSize % granularity, 0);
    EXPECT_GE(actualSize, requestedSize);

    freeVirtualMemory(&vmem);
}

TEST_F(VMemBasicTest, InitPatternWorks) {
    SimplifiedVirtualMemory vmem;
    const int N = 1024;
    const int offset = 100;

    ASSERT_TRUE(initVirtualMemory(&vmem, N * sizeof(int)));

    int* d_data = static_cast<int*>(getVirtualPtr(&vmem));
    init_vmem_pattern<<<(N+255)/256, 256>>>(d_data, N, offset);
    CHECK_KERNEL_LAUNCH();

    // Verify pattern
    std::vector<int> h_data(N);
    cuda_memcpy_d2h(h_data.data(), d_data, N);

    for (int i = 0; i < N; i++) {
        EXPECT_EQ(h_data[i], i + offset);
    }

    freeVirtualMemory(&vmem);
}

TEST_F(VMemBasicTest, VerifyPatternWorks) {
    SimplifiedVirtualMemory vmem;
    const int N = 1024;
    const int offset = 50;

    ASSERT_TRUE(initVirtualMemory(&vmem, N * sizeof(int)));

    int* d_data = static_cast<int*>(getVirtualPtr(&vmem));

    // Initialize pattern
    init_vmem_pattern<<<(N+255)/256, 256>>>(d_data, N, offset);
    CHECK_KERNEL_LAUNCH();

    // Verify pattern on device
    bool* d_result = cuda_malloc<bool>(1);
    bool h_result = true;
    cuda_memcpy_h2d(d_result, &h_result, 1);

    verify_vmem_pattern<<<(N+255)/256, 256>>>(d_data, N, offset, d_result);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy_d2h(&h_result, d_result, 1);
    EXPECT_TRUE(h_result);

    cuda_free(d_result);
    freeVirtualMemory(&vmem);
}

TEST_F(VMemBasicTest, StrideAccessWorks) {
    SimplifiedVirtualMemory vmem_in, vmem_out;
    const int N = 256;
    const int stride = 3;

    ASSERT_TRUE(initVirtualMemory(&vmem_in, N * sizeof(int)));
    ASSERT_TRUE(initVirtualMemory(&vmem_out, N * sizeof(int)));

    int* d_input = static_cast<int*>(getVirtualPtr(&vmem_in));
    int* d_output = static_cast<int*>(getVirtualPtr(&vmem_out));

    // Initialize input
    init_vmem_pattern<<<(N+255)/256, 256>>>(d_input, N, 0);
    CHECK_KERNEL_LAUNCH();

    // Strided access
    vmem_stride_access<<<(N+255)/256, 256>>>(d_output, d_input, N, stride);
    CHECK_KERNEL_LAUNCH();

    // Verify
    std::vector<int> h_output(N);
    cuda_memcpy_d2h(h_output.data(), d_output, N);

    for (int i = 0; i < N; i++) {
        int expected = (i * stride) % N;
        EXPECT_EQ(h_output[i], expected);
    }

    freeVirtualMemory(&vmem_in);
    freeVirtualMemory(&vmem_out);
}

TEST_F(VMemBasicTest, SharedMemoryReduceWorks) {
    SimplifiedVirtualMemory vmem_in, vmem_out;
    const int N = 1024;
    const int blockSize = 256;
    const int gridSize = (N + blockSize - 1) / blockSize;

    ASSERT_TRUE(initVirtualMemory(&vmem_in, N * sizeof(int)));
    ASSERT_TRUE(initVirtualMemory(&vmem_out, gridSize * sizeof(int)));

    int* d_input = static_cast<int*>(getVirtualPtr(&vmem_in));
    int* d_output = static_cast<int*>(getVirtualPtr(&vmem_out));

    // Initialize input with ones
    init_vmem_pattern<<<(N+255)/256, 256>>>(d_input, N, 1);
    CHECK_KERNEL_LAUNCH();

    // Reduce
    vmem_shared_reduce<<<gridSize, blockSize>>>(d_output, d_input, N);
    CHECK_KERNEL_LAUNCH();

    // Verify partial sums
    std::vector<int> h_output(gridSize);
    cuda_memcpy_d2h(h_output.data(), d_output, gridSize);

    // Each block should sum its elements
    for (int i = 0; i < gridSize; i++) {
        int blockStart = i * blockSize;
        int blockEnd = std::min((i + 1) * blockSize, N);

        // Sum should be: sum of (idx + 1) for idx in [blockStart, blockEnd)
        int expectedSum = 0;
        for (int idx = blockStart; idx < blockEnd; idx++) {
            expectedSum += idx + 1;
        }

        EXPECT_EQ(h_output[i], expectedSum);
    }

    freeVirtualMemory(&vmem_in);
    freeVirtualMemory(&vmem_out);
}

TEST_F(VMemBasicTest, CoalescedCopyWorks) {
    SimplifiedVirtualMemory vmem_in, vmem_out;
    const int N = 1024;

    ASSERT_TRUE(initVirtualMemory(&vmem_in, N * sizeof(int)));
    ASSERT_TRUE(initVirtualMemory(&vmem_out, N * sizeof(int)));

    int* d_input = static_cast<int*>(getVirtualPtr(&vmem_in));
    int* d_output = static_cast<int*>(getVirtualPtr(&vmem_out));

    // Initialize input
    init_vmem_pattern<<<(N+255)/256, 256>>>(d_input, N, 0);
    CHECK_KERNEL_LAUNCH();

    // Coalesced copy
    vmem_coalesced_copy<<<(N+255)/256, 256>>>(d_output, d_input, N);
    CHECK_KERNEL_LAUNCH();

    // Verify
    std::vector<int> h_output(N);
    cuda_memcpy_d2h(h_output.data(), d_output, N);

    for (int i = 0; i < N; i++) {
        EXPECT_EQ(h_output[i], i);
    }

    freeVirtualMemory(&vmem_in);
    freeVirtualMemory(&vmem_out);
}

TEST_F(VMemBasicTest, UncoalescedCopyWorks) {
    SimplifiedVirtualMemory vmem_in, vmem_out;
    const int N = 1024;

    ASSERT_TRUE(initVirtualMemory(&vmem_in, N * sizeof(int)));
    ASSERT_TRUE(initVirtualMemory(&vmem_out, N * sizeof(int)));

    int* d_input = static_cast<int*>(getVirtualPtr(&vmem_in));
    int* d_output = static_cast<int*>(getVirtualPtr(&vmem_out));

    // Initialize input
    init_vmem_pattern<<<(N+255)/256, 256>>>(d_input, N, 0);
    CHECK_KERNEL_LAUNCH();

    // Uncoalesced copy
    vmem_uncoalesced_copy<<<(N+255)/256, 256>>>(d_output, d_input, N);
    CHECK_KERNEL_LAUNCH();

    // Verify - output should be reversed
    std::vector<int> h_output(N);
    cuda_memcpy_d2h(h_output.data(), d_output, N);

    for (int i = 0; i < N; i++) {
        int expected = N - 1 - i;
        EXPECT_EQ(h_output[i], expected);
    }

    freeVirtualMemory(&vmem_in);
    freeVirtualMemory(&vmem_out);
}

TEST_F(VMemBasicTest, MultipleVirtualMemoryAllocations) {
    const int NUM_ALLOCS = 5;
    SimplifiedVirtualMemory vmems[NUM_ALLOCS];

    // Allocate multiple virtual memory regions
    for (int i = 0; i < NUM_ALLOCS; i++) {
        size_t size = (i + 1) * 1024 * sizeof(int);
        ASSERT_TRUE(initVirtualMemory(&vmems[i], size));
        EXPECT_NE(getVirtualPtr(&vmems[i]), nullptr);
    }

    // Verify all are unique
    for (int i = 0; i < NUM_ALLOCS; i++) {
        for (int j = i + 1; j < NUM_ALLOCS; j++) {
            EXPECT_NE(getVirtualPtr(&vmems[i]), getVirtualPtr(&vmems[j]));
        }
    }

    // Free all
    for (int i = 0; i < NUM_ALLOCS; i++) {
        freeVirtualMemory(&vmems[i]);
    }
}
