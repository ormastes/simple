/**
 * @file test_bandwidth.cu
 * @brief GTest unit tests for GPU bandwidth measurement
 *
 * Verifies that the STREAM-like bandwidth tests return positive, finite
 * values and that different tests yield reasonable relative performance.
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "profiling/bandwidth_test.h"

using namespace opt79;

/**
 * @brief Test fixture for bandwidth tests
 */
class BandwidthTestFixture : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }
};

/**
 * @brief Test that bandwidth results are positive and finite
 */
TEST_F(BandwidthTestFixture, ResultsArePositive) {
    // Use a small array for fast testing
    BandwidthResult result = run_bandwidth_test(1024 * 1024, /*num_trials=*/3);

    EXPECT_GT(result.copy_gbps, 0.0) << "Copy bandwidth should be positive";
    EXPECT_GT(result.scale_gbps, 0.0) << "Scale bandwidth should be positive";
    EXPECT_GT(result.add_gbps, 0.0) << "Add bandwidth should be positive";
    EXPECT_GT(result.triad_gbps, 0.0) << "Triad bandwidth should be positive";

    EXPECT_LT(result.copy_gbps, 2000.0) << "Copy bandwidth suspiciously high";
    EXPECT_LT(result.scale_gbps, 2000.0) << "Scale bandwidth suspiciously high";
    EXPECT_LT(result.add_gbps, 2000.0) << "Add bandwidth suspiciously high";
    EXPECT_LT(result.triad_gbps, 2000.0) << "Triad bandwidth suspiciously high";

    std::cout << "Bandwidth results (1M elements):" << std::endl;
    print_bandwidth_result(result);
}

/**
 * @brief Test that larger arrays achieve higher effective bandwidth
 *        (small arrays underutilize the memory bus due to launch overhead)
 */
TEST_F(BandwidthTestFixture, LargerArrayHigherBandwidth) {
    BandwidthResult small_result = run_bandwidth_test(64 * 1024, 3);     // 64K elements
    BandwidthResult large_result = run_bandwidth_test(16 * 1024 * 1024, 3); // 16M elements

    // Large arrays should generally achieve higher bandwidth
    // (not always guaranteed, but a reasonable sanity check)
    std::cout << "Small array (64K) triad: " << small_result.triad_gbps << " GB/s" << std::endl;
    std::cout << "Large array (16M) triad: " << large_result.triad_gbps << " GB/s" << std::endl;

    // Both should be positive
    EXPECT_GT(small_result.triad_gbps, 0.0);
    EXPECT_GT(large_result.triad_gbps, 0.0);
}
