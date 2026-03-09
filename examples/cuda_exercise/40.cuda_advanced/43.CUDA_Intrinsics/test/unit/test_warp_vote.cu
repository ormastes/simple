// test_warp_vote.cu - Tests for warp voting intrinsics

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "kernels/warp_vote.cu"

class WarpVoteTest : public GpuTest {};

TEST_F(WarpVoteTest, WarpAllDetectsAllThreadsMeetingCondition) {
    const int N = 32;  // One warp
    int* h_input = new int[N];
    int* h_output = new int[N];

    // Test case 1: All values above threshold
    for (int i = 0; i < N; i++) {
        h_input[i] = 100;  // All above threshold 50
    }

    int* d_input = cuda_malloc<int>(N);
    int* d_output = cuda_malloc<int>(N);

    cuda_memcpy_h2d(d_input, h_input, N);

    warp_all_kernel<<<1, 32>>>(d_output, d_input, N, 50);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy_d2h(h_output, d_output, N);

    // All threads should report true (1)
    for (int i = 0; i < N; i++) {
        EXPECT_EQ(h_output[i], 1) << "Expected all threads to meet condition at " << i;
    }

    // Test case 2: One value below threshold
    h_input[15] = 10;  // One below threshold
    cuda_memcpy_h2d(d_input, h_input, N);

    warp_all_kernel<<<1, 32>>>(d_output, d_input, N, 50);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy_d2h(h_output, d_output, N);

    // All threads should report false (0)
    for (int i = 0; i < N; i++) {
        EXPECT_EQ(h_output[i], 0) << "Expected no threads to meet all condition at " << i;
    }

    cuda_free(d_input);
    cuda_free(d_output);
    delete[] h_input;
    delete[] h_output;
}

TEST_F(WarpVoteTest, WarpAnyDetectsSomeThreadsMeetingCondition) {
    const int N = 32;  // One warp
    int* h_input = new int[N];
    int* h_output = new int[N];

    // Test case 1: No values above threshold
    for (int i = 0; i < N; i++) {
        h_input[i] = 10;  // All below threshold 50
    }

    int* d_input = cuda_malloc<int>(N);
    int* d_output = cuda_malloc<int>(N);

    cuda_memcpy_h2d(d_input, h_input, N);

    warp_any_kernel<<<1, 32>>>(d_output, d_input, N, 50);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy_d2h(h_output, d_output, N);

    // All threads should report false (0)
    for (int i = 0; i < N; i++) {
        EXPECT_EQ(h_output[i], 0) << "Expected no threads to detect any at " << i;
    }

    // Test case 2: One value above threshold
    h_input[20] = 100;  // One above threshold
    cuda_memcpy_h2d(d_input, h_input, N);

    warp_any_kernel<<<1, 32>>>(d_output, d_input, N, 50);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy_d2h(h_output, d_output, N);

    // All threads should report true (1)
    for (int i = 0; i < N; i++) {
        EXPECT_EQ(h_output[i], 1) << "Expected all threads to detect any at " << i;
    }

    cuda_free(d_input);
    cuda_free(d_output);
    delete[] h_input;
    delete[] h_output;
}

TEST_F(WarpVoteTest, WarpBallotCountsThreadsMeetingCondition) {
    const int N = 32;  // One warp
    int* h_input = new int[N];
    unsigned int* h_output = new unsigned int[N];

    // Set up: 10 threads meet condition
    for (int i = 0; i < N; i++) {
        h_input[i] = (i < 10) ? 100 : 10;  // First 10 meet threshold
    }

    int* d_input = cuda_malloc<int>(N);
    unsigned int* d_output = cuda_malloc<unsigned int>(N);

    cuda_memcpy_h2d(d_input, h_input, N);

    warp_ballot_kernel<<<1, 32>>>(d_output, d_input, N, 50);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy_d2h(h_output, d_output, N);

    // All threads should report count of 10
    for (int i = 0; i < N; i++) {
        EXPECT_EQ(h_output[i], 10u) << "Expected count of 10 at index " << i;
    }

    cuda_free(d_input);
    cuda_free(d_output);
    delete[] h_input;
    delete[] h_output;
}

TEST_F(WarpVoteTest, WarpMatchFindsThreadsWithSameValue) {
    const int N = 32;  // One warp
    int* h_input = new int[N];
    unsigned long long* h_output = new unsigned long long[N];

    // Set up: threads 0-9 have value 42, threads 10-19 have value 99, rest have unique values
    for (int i = 0; i < N; i++) {
        if (i < 10) {
            h_input[i] = 42;
        } else if (i < 20) {
            h_input[i] = 99;
        } else {
            h_input[i] = i;  // Unique values
        }
    }

    int* d_input = cuda_malloc<int>(N);
    unsigned long long* d_output = cuda_malloc<unsigned long long>(N);

    cuda_memcpy_h2d(d_input, h_input, N);

    warp_match_kernel<<<1, 32>>>(d_output, d_input, N);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy_d2h(h_output, d_output, N);

    // Threads 0-9 should have same match mask
    unsigned int first_mask = h_output[0];
    for (int i = 1; i < 10; i++) {
        EXPECT_EQ(h_output[i], first_mask) << "Threads with value 42 should match at " << i;
    }

    // Count bits in first mask should be 10
    int count = __builtin_popcount(first_mask);
    EXPECT_EQ(count, 10) << "Expected 10 threads to match value 42";

    // Threads 10-19 should have same match mask
    unsigned int second_mask = h_output[10];
    for (int i = 11; i < 20; i++) {
        EXPECT_EQ(h_output[i], second_mask) << "Threads with value 99 should match at " << i;
    }

    count = __builtin_popcount(second_mask);
    EXPECT_EQ(count, 10) << "Expected 10 threads to match value 99";

    // Threads 20-31 should have unique masks (only 1 bit set)
    for (int i = 20; i < N; i++) {
        count = __builtin_popcount(h_output[i]);
        EXPECT_EQ(count, 1) << "Thread " << i << " should have unique value";
    }

    cuda_free(d_input);
    cuda_free(d_output);
    delete[] h_input;
    delete[] h_output;
}

TEST_F(WarpVoteTest, WarpCompactRemovesZeros) {
    const int N = 32;  // One warp
    int* h_input = new int[N];
    int* h_output = new int[N];
    int h_count = 0;

    // Set up: sparse array with some non-zeros
    for (int i = 0; i < N; i++) {
        h_input[i] = (i % 5 == 0) ? (i + 1) : 0;  // Non-zero at indices 0, 5, 10, 15, 20, 25, 30
    }

    int* d_input = cuda_malloc<int>(N);
    int* d_output = cuda_malloc<int>(N);
    int* d_count = cuda_malloc<int>(1);
    cuda_memset(d_output, 0, N);
    cuda_memset(d_count, 0, 1);

    cuda_memcpy_h2d(d_input, h_input, N);

    warp_compact_kernel<<<1, 32>>>(d_output, d_count, d_input, N);
    CHECK_KERNEL_LAUNCH();

    cuda_memcpy_d2h(h_output, d_output, N);
    cuda_memcpy_d2h(&h_count, d_count, 1);

    // Verify count: should be 7 non-zero values
    EXPECT_EQ(h_count, 7) << "Expected 7 non-zero values";

    // Verify compacted values (should be 1, 6, 11, 16, 21, 26, 31 in first 7 positions)
    int expected_values[] = {1, 6, 11, 16, 21, 26, 31};
    for (int i = 0; i < 7; i++) {
        EXPECT_EQ(h_output[i], expected_values[i]) << "Compacted value mismatch at " << i;
    }

    cuda_free(d_input);
    cuda_free(d_output);
    cuda_free(d_count);
    delete[] h_input;
    delete[] h_output;
}
