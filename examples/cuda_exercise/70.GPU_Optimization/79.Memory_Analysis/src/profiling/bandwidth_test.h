/**
 * @file bandwidth_test.h
 * @brief STREAM-like GPU memory bandwidth benchmarks.
 */

#pragma once
#include <cstddef>

namespace opt79 {

/**
 * @brief Result of a bandwidth test run.
 *
 * Contains measured bandwidth in GB/s for Copy, Scale, Add, and Triad operations.
 */
struct BandwidthResult {
    double copy_gbps;   ///< Copy bandwidth (c=a) in GB/s
    double scale_gbps;  ///< Scale bandwidth (b=s*c) in GB/s
    double add_gbps;    ///< Add bandwidth (c=a+b) in GB/s
    double triad_gbps;  ///< Triad bandwidth (a=b+s*c) in GB/s
};

/**
 * @brief Run STREAM-like bandwidth tests on GPU global memory.
 *
 * Allocates three float arrays of the given size, runs Copy, Scale, Add,
 * and Triad operations, measures bandwidth using CUDA events, and returns
 * the best result across multiple trials.
 *
 * @param[in] num_elements Number of float elements per array
 * @param[in] num_trials   Number of iterations (best time is reported)
 * @return BandwidthResult with all four measurements
 */
BandwidthResult run_bandwidth_test(size_t num_elements, int num_trials = 10);

/// @brief Print bandwidth results to stdout
void print_bandwidth_result(const BandwidthResult& r);

}  // namespace opt79
