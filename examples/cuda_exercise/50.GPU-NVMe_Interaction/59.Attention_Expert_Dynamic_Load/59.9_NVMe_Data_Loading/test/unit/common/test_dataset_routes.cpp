#include <gtest/gtest.h>

#include "dataset_routes.h"

namespace {

using dataset59::buildDatasetPlan;

TEST(DatasetPlanTest, IncludesExpertWeightsRoute) {
    const auto plan = buildDatasetPlan();
    bool found = false;
    for (const auto& route : plan.routes) {
        if (route.name == "Expert Weights") {
            found = true;
        }
    }
    EXPECT_TRUE(found);
}

TEST(DatasetPlanTest, RouteCountAtLeastThree) {
    const auto plan = buildDatasetPlan();
    EXPECT_GE(plan.routeCount(), 3u);
}

}  // namespace
