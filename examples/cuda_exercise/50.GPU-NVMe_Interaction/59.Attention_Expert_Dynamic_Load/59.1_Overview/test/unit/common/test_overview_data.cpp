#include <gtest/gtest.h>

#include "overview_data.h"

namespace {

using overview59::buildDefaultOverview;
using overview59::formatOverview;

TEST(OverviewSummaryTest, ContainsExpectedLayerCount) {
    const auto summary = buildDefaultOverview();
    EXPECT_EQ(summary.layerCount(), 4u);
    EXPECT_EQ(summary.components[0].name, "Python API Layer");
}

TEST(OverviewSummaryTest, FormatOverviewProducesReadableText) {
    const auto summary = buildDefaultOverview();
    const std::string formatted = formatOverview(summary);
    EXPECT_NE(formatted.find("architectural layers"), std::string::npos);
    EXPECT_NE(formatted.find("CUDA Kernel Layer"), std::string::npos);
}

}  // namespace
