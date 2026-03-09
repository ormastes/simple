/**
 * @file test_memory_profiler.cu
 * @brief GTest unit tests for the MemoryTracker.
 *
 * Verifies tracked allocation, deallocation, peak tracking, leak detection,
 * and the free_all utility.
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "profiling/memory_profiler.h"

using namespace opt79;

/**
 * @brief Test fixture for MemoryTracker tests
 */
class MemoryProfilerTest : public GpuTest {
protected:
    MemoryTracker tracker;

    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        tracker.free_all();
        GpuTest::TearDown();
    }
};

/**
 * @brief Test basic allocation and deallocation tracking
 */
TEST_F(MemoryProfilerTest, AllocAndFree) {
    void* p = tracker.tracked_malloc(1024, "test_block");
    ASSERT_NE(p, nullptr) << "tracked_malloc returned nullptr";
    EXPECT_EQ(tracker.allocations.size(), 1u);
    EXPECT_EQ(tracker.current_usage, 1024u);

    tracker.tracked_free(p);
    EXPECT_EQ(tracker.allocations.size(), 0u);
    EXPECT_EQ(tracker.current_usage, 0u);
}

/**
 * @brief Test peak usage tracking across multiple allocations
 */
TEST_F(MemoryProfilerTest, PeakUsage) {
    void* p1 = tracker.tracked_malloc(4096, "block_a");
    void* p2 = tracker.tracked_malloc(8192, "block_b");
    EXPECT_EQ(tracker.peak_usage, 4096u + 8192u);

    tracker.tracked_free(p1);
    EXPECT_EQ(tracker.current_usage, 8192u);
    EXPECT_EQ(tracker.peak_usage, 4096u + 8192u)
        << "Peak should not decrease after free";

    tracker.tracked_free(p2);
    EXPECT_EQ(tracker.current_usage, 0u);
    EXPECT_EQ(tracker.peak_usage, 4096u + 8192u);
}

/**
 * @brief Test leak detection reports unfree'd allocations
 */
TEST_F(MemoryProfilerTest, LeakDetection) {
    tracker.tracked_malloc(2048, "leak_block");
    EXPECT_EQ(tracker.check_leaks(), 1u);

    // free_all in TearDown will clean up
}

/**
 * @brief Test free_all clears all allocations
 */
TEST_F(MemoryProfilerTest, FreeAll) {
    tracker.tracked_malloc(1024, "a");
    tracker.tracked_malloc(2048, "b");
    tracker.tracked_malloc(4096, "c");
    EXPECT_EQ(tracker.allocations.size(), 3u);

    tracker.free_all();
    EXPECT_EQ(tracker.allocations.size(), 0u);
    EXPECT_EQ(tracker.current_usage, 0u);
}

/**
 * @brief Test that allocated memory is actually usable
 */
TEST_F(MemoryProfilerTest, MemoryIsUsable) {
    size_t n = 256;
    void* p = tracker.tracked_malloc(n * sizeof(float), "usable_block");
    ASSERT_NE(p, nullptr);

    // Write pattern and read back
    float* d_data = static_cast<float*>(p);
    std::vector<float> h_data(n, 42.0f);
    CHECK_CUDA(cudaMemcpy(d_data, h_data.data(), n * sizeof(float), cudaMemcpyHostToDevice));

    std::vector<float> h_result(n, 0.0f);
    CHECK_CUDA(cudaMemcpy(h_result.data(), d_data, n * sizeof(float), cudaMemcpyDeviceToHost));

    for (size_t i = 0; i < n; ++i) {
        EXPECT_FLOAT_EQ(h_result[i], 42.0f);
    }

    tracker.tracked_free(p);
}
