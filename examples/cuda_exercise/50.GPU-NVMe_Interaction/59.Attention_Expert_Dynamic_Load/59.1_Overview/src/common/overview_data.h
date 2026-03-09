/**
 * @file overview_data.h
 * @brief Module 59.1 overview data structures
 */

#pragma once

#include <cstddef>
#include <string>
#include <vector>

namespace overview59 {

/**
 * @brief Describes a single architectural component.
 */
struct OverviewComponent {
    std::string name;
    std::string description;
};

/**
 * @brief Canonical summary for Module 59 showing all logical layers.
 */
struct OverviewSummary {
    std::string module_name;
    std::vector<OverviewComponent> components;

    [[nodiscard]] std::size_t layerCount() const noexcept {
        return components.size();
    }
};

/**
 * @brief Build default overview summary
 * @return Overview summary with default components
 */
OverviewSummary buildDefaultOverview();

/**
 * @brief Format overview summary for display
 * @param summary Overview summary to format
 * @return Formatted string
 */
std::string formatOverview(const OverviewSummary& summary);

/**
 * @brief Populate device memory with layer count
 * @param device_ptr Device memory pointer
 * @param layer_count Number of layers
 */
void populateDeviceLayerCount(int* device_ptr, int layer_count);

}  // namespace overview59
