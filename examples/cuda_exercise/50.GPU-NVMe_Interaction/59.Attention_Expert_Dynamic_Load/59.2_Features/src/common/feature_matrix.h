/**
 * @file feature_matrix.h
 * @brief Module 59.2 feature matrix data structures
 */

#pragma once

#include "overview_data.h"

#include <string>
#include <vector>

namespace features59 {

/**
 * @brief Describes a single feature capability.
 */
struct FeatureEntry {
    std::string name;
    std::string support;
    std::string notes;
    overview59::OverviewComponent source_layer;
};

/**
 * @brief Collection of features mapped to Module 59.1 overview layers.
 */
struct FeatureMatrix {
    std::vector<FeatureEntry> entries;

    [[nodiscard]] std::size_t featureCount() const noexcept {
        return entries.size();
    }
};

/**
 * @brief Build default feature matrix
 * @return Feature matrix with default entries
 */
FeatureMatrix buildDefaultMatrix();

/**
 * @brief Format feature matrix for display
 * @param matrix Feature matrix to format
 * @return Formatted string
 */
std::string formatMatrix(const FeatureMatrix& matrix);

/**
 * @brief Populate device memory with feature count
 * @param device_ptr Device memory pointer
 * @param feature_count Number of features
 */
void populateDeviceFeatureCount(int* device_ptr, int feature_count);

}  // namespace features59
