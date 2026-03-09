#include <gtest/gtest.h>

#include "perf_scenarios.h"

namespace {

using perf59::buildPerfPlan;

TEST(PerfPlanTest, ContainsNsightSystemsScenario) {
    const auto plan = buildPerfPlan();
    bool found_nsys = false;
    for (const auto& scenario : plan.scenarios) {
        if (scenario.profiler_command.find("nsys") != std::string::npos) {
            found_nsys = true;
        }
    }
    EXPECT_TRUE(found_nsys);
}

TEST(PerfPlanTest, ScenarioCountAtLeastThree) {
    const auto plan = buildPerfPlan();
    EXPECT_GE(plan.scenarioCount(), 3u);
}

}  // namespace
