/**
 * @file dispatcher_checks.h
 * @brief Module 59.5 PyTorch dispatcher checks
 */

#pragma once

#include "example_registry.h"

#include <string>
#include <vector>

namespace torch59 {

/**
 * @brief PyTorch dispatcher check entry
 */
struct DispatcherCheck {
    std::string name;
    std::string status;
    std::string dispatch_key;
    examples59::ExampleSnippet reference_example;
};

/**
 * @brief Collection of dispatcher checks
 */
struct DispatcherMatrix {
    std::vector<DispatcherCheck> checks;

    [[nodiscard]] std::size_t checkCount() const noexcept {
        return checks.size();
    }
};

/**
 * @brief Build dispatcher matrix
 * @return Dispatcher matrix with default checks
 */
DispatcherMatrix buildDispatcherMatrix();

/**
 * @brief Format matrix for display
 * @param matrix Dispatcher matrix to format
 * @return Formatted string
 */
std::string formatMatrix(const DispatcherMatrix& matrix);

/**
 * @brief Populate device memory with check count
 * @param device_ptr Device memory pointer
 * @param check_count Number of checks
 */
void populateDeviceCheckCount(int* device_ptr, int check_count);

}  // namespace torch59
