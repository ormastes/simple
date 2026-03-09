/**
 * @file build_recipe.h
 * @brief Module 59.3 build recipe data structures
 */

#pragma once

#include "feature_matrix.h"

#include <string>
#include <vector>

namespace build59 {

/**
 * @brief Build step with command and notes
 */
struct BuildStep {
    std::string name;
    std::string command;
    std::string note;
    features59::FeatureEntry related_feature;
};

/**
 * @brief Collection of build steps
 */
struct BuildRecipe {
    std::vector<BuildStep> steps;

    [[nodiscard]] std::size_t stepCount() const noexcept {
        return steps.size();
    }
};

/**
 * @brief Build default build recipe
 * @return Build recipe with default steps
 */
BuildRecipe buildDefaultRecipe();

/**
 * @brief Format build recipe for display
 * @param recipe Build recipe to format
 * @return Formatted string
 */
std::string formatRecipe(const BuildRecipe& recipe);

/**
 * @brief Populate device memory with step count
 * @param device_ptr Device memory pointer
 * @param step_count Number of steps
 */
void populateDeviceStepCount(int* device_ptr, int step_count);

}  // namespace build59
