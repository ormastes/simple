#include <gtest/gtest.h>

#include "build_recipe.h"

namespace {

using build59::buildDefaultRecipe;

TEST(BuildRecipeTest, ContainsExpectedSteps) {
    const auto recipe = buildDefaultRecipe();
    EXPECT_GE(recipe.stepCount(), 4u);
    EXPECT_EQ(recipe.steps.front().name, "Configure CMake");
}

TEST(BuildRecipeTest, CommandsIncludeNinjaAndPip) {
    const auto recipe = buildDefaultRecipe();
    bool has_ninja = false;
    bool has_pip = false;
    for (const auto& step : recipe.steps) {
        if (step.command.find("ninja") != std::string::npos) {
            has_ninja = true;
        }
        if (step.command.find("pip") != std::string::npos) {
            has_pip = true;
        }
    }
    EXPECT_TRUE(has_ninja);
    EXPECT_TRUE(has_pip);
}

}  // namespace
