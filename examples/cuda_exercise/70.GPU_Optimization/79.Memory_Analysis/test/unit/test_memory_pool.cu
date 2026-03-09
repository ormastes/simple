/**
 * @file test_memory_pool.cu
 * @brief GTest unit tests for the free-list memory pool allocator
 *
 * Tests pool initialization, allocation, deallocation, coalescing,
 * and out-of-memory handling.
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "optimizations/memory_pool.h"

using namespace opt79;

/**
 * @brief Test fixture for MemoryPool tests
 */
class MemoryPoolTest : public GpuTest {
protected:
    static constexpr size_t POOL_SIZE = 1 * 1024 * 1024;  // 1 MB

    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }
};

/**
 * @brief Test pool initialization and basic allocation
 */
TEST_F(MemoryPoolTest, InitAndAllocate) {
    MemoryPool pool(POOL_SIZE);
    ASSERT_TRUE(pool.init()) << "Pool initialization failed";
    EXPECT_EQ(pool.total_bytes(), POOL_SIZE);
    EXPECT_EQ(pool.used_bytes(), 0u);

    void* p = pool.allocate(1024);
    ASSERT_NE(p, nullptr) << "Pool allocation returned nullptr";
    EXPECT_GT(pool.used_bytes(), 0u);

    pool.deallocate(p);
    pool.destroy();
}

/**
 * @brief Test multiple allocations and deallocations
 */
TEST_F(MemoryPoolTest, MultipleAllocations) {
    MemoryPool pool(POOL_SIZE);
    ASSERT_TRUE(pool.init());

    void* p1 = pool.allocate(4096);
    void* p2 = pool.allocate(8192);
    void* p3 = pool.allocate(1024);

    ASSERT_NE(p1, nullptr);
    ASSERT_NE(p2, nullptr);
    ASSERT_NE(p3, nullptr);

    // All pointers should be different
    EXPECT_NE(p1, p2);
    EXPECT_NE(p2, p3);
    EXPECT_NE(p1, p3);

    size_t used_before = pool.used_bytes();
    pool.deallocate(p2);
    EXPECT_LT(pool.used_bytes(), used_before);

    pool.deallocate(p1);
    pool.deallocate(p3);
    pool.destroy();
}

/**
 * @brief Test coalescing of adjacent free blocks
 */
TEST_F(MemoryPoolTest, Coalescing) {
    MemoryPool pool(POOL_SIZE);
    ASSERT_TRUE(pool.init());

    // Allocate three blocks
    void* p1 = pool.allocate(1024);
    void* p2 = pool.allocate(1024);
    void* p3 = pool.allocate(1024);
    ASSERT_NE(p1, nullptr);
    ASSERT_NE(p2, nullptr);
    ASSERT_NE(p3, nullptr);

    size_t free_before = pool.num_free_blocks();

    // Free middle block
    pool.deallocate(p2);
    // Free first block - should coalesce with p2's freed block
    pool.deallocate(p1);

    // After coalescing, free blocks should not increase beyond expectation
    // (p1+p2 merged into one free block, plus the remainder block)
    EXPECT_LE(pool.num_free_blocks(), 3u);

    pool.deallocate(p3);
    // After freeing everything, should coalesce to one free block
    EXPECT_EQ(pool.num_free_blocks(), 1u);

    pool.destroy();
}

/**
 * @brief Test out-of-memory returns nullptr
 */
TEST_F(MemoryPoolTest, OutOfMemory) {
    size_t small_pool = 4096;  // 4 KB pool
    MemoryPool pool(small_pool);
    ASSERT_TRUE(pool.init());

    // Try to allocate more than the pool size
    void* p = pool.allocate(small_pool + 1024);
    EXPECT_EQ(p, nullptr) << "Should return nullptr when out of pool memory";

    pool.destroy();
}

/**
 * @brief Test that pool-allocated memory is usable for CUDA operations
 */
TEST_F(MemoryPoolTest, MemoryIsUsable) {
    MemoryPool pool(POOL_SIZE);
    ASSERT_TRUE(pool.init());

    size_t n = 128;
    void* p = pool.allocate(n * sizeof(float));
    ASSERT_NE(p, nullptr);

    float* d_data = static_cast<float*>(p);
    std::vector<float> h_data(n, 99.0f);
    CHECK_CUDA(cudaMemcpy(d_data, h_data.data(), n * sizeof(float), cudaMemcpyHostToDevice));

    std::vector<float> h_result(n, 0.0f);
    CHECK_CUDA(cudaMemcpy(h_result.data(), d_data, n * sizeof(float), cudaMemcpyDeviceToHost));

    for (size_t i = 0; i < n; ++i) {
        EXPECT_FLOAT_EQ(h_result[i], 99.0f);
    }

    pool.deallocate(p);
    pool.destroy();
}
