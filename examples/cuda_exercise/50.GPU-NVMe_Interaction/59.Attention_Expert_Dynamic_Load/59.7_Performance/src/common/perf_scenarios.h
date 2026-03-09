/**
 * @file perf_scenarios.h
 * @brief Module 59.7 performance scenarios
 */

#pragma once

#include "nvme_modes.h"

#include <string>
#include <vector>

namespace perf59 {

/**
 * @brief Performance profiling scenario
 */
struct PerfScenario {
    std::string name;
    std::string profiler_command;
    std::string metric;
    nvme59::NvmeModeEntry nvme_mode;
};

/**
 * @brief Collection of performance scenarios
 */
struct PerfPlan {
    std::vector<PerfScenario> scenarios;

    [[nodiscard]] std::size_t scenarioCount() const noexcept {
        return scenarios.size();
    }
};

/**
 * @brief Build performance plan
 * @return Performance plan with default scenarios
 */
PerfPlan buildPerfPlan();

/**
 * @brief Format plan for display
 * @param plan Performance plan to format
 * @return Formatted string
 */
std::string formatPlan(const PerfPlan& plan);

/**
 * @brief Populate device memory with scenario count
 * @param device_ptr Device memory pointer
 * @param scenario_count Number of scenarios
 */
void populateDeviceScenarioCount(int* device_ptr, int scenario_count);

}  // namespace perf59
