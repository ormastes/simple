/**
 * @file test_matrix.h
 * @brief Module 59.8 test matrix
 */

#pragma once

#include "perf_scenarios.h"

#include <string>
#include <vector>

namespace testing59 {

/**
 * @brief Test case entry
 */
struct TestEntry {
    std::string name;
    std::string command;
    std::string type;
    perf59::PerfScenario scenario;
};

/**
 * @brief Collection of test cases
 */
struct TestMatrix {
    std::vector<TestEntry> entries;

    [[nodiscard]] std::size_t testCount() const noexcept {
        return entries.size();
    }
};

/**
 * @brief Build test matrix
 * @return Test matrix with default entries
 */
TestMatrix buildTestMatrix();

/**
 * @brief Format matrix for display
 * @param matrix Test matrix to format
 * @return Formatted string
 */
std::string formatMatrix(const TestMatrix& matrix);

/**
 * @brief Populate device memory with test count
 * @param device_ptr Device memory pointer
 * @param test_count Number of tests
 */
void populateDeviceTestCount(int* device_ptr, int test_count);

}  // namespace testing59
