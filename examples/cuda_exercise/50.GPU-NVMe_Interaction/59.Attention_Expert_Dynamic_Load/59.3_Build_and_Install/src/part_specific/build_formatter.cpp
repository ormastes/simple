#include "build_recipe.h"

#include <sstream>

namespace build59 {

std::string formatRecipe(const BuildRecipe& recipe) {
    std::ostringstream oss;
    oss << "Build & Install Recipe (" << recipe.stepCount() << " steps)\n";
    std::size_t index = 1;
    for (const auto& step : recipe.steps) {
        oss << "  [" << index++ << "] " << step.name << "\n"
            << "      Command: " << step.command << "\n"
            << "      Feature: " << step.related_feature.name << "\n"
            << "      Note: " << step.note << '\n';
    }
    return oss.str();
}

}  // namespace build59
