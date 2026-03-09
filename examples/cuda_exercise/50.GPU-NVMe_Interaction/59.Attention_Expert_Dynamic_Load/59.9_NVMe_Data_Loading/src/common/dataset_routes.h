/**
 * @file dataset_routes.h
 * @brief Module 59.9 dataset routes
 */

#pragma once

#include "test_matrix.h"

#include <string>
#include <vector>

namespace dataset59 {

/**
 * @brief Dataset route entry
 */
struct DatasetRoute {
    std::string name;
    std::string nvme_device;
    std::string tensor_shape;
    testing59::TestEntry validating_test;
};

/**
 * @brief Collection of dataset routes
 */
struct DatasetPlan {
    std::vector<DatasetRoute> routes;

    [[nodiscard]] std::size_t routeCount() const noexcept {
        return routes.size();
    }
};

/**
 * @brief Build dataset plan
 * @return Dataset plan with default routes
 */
DatasetPlan buildDatasetPlan();

/**
 * @brief Format plan for display
 * @param plan Dataset plan to format
 * @return Formatted string
 */
std::string formatPlan(const DatasetPlan& plan);

/**
 * @brief Populate device memory with route count
 * @param device_ptr Device memory pointer
 * @param route_count Number of routes
 */
void populateDeviceRouteCount(int* device_ptr, int route_count);

}  // namespace dataset59
