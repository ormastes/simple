#include <gtest/gtest.h>

#include "feature_matrix.h"

namespace {

using features59::buildDefaultMatrix;

TEST(FeatureMatrixTest, ExpectedFeatureCount) {
    const auto matrix = buildDefaultMatrix();
    EXPECT_GE(matrix.featureCount(), 6u);
}

TEST(FeatureMatrixTest, AllFeaturesMapToOverviewLayer) {
    const auto matrix = buildDefaultMatrix();
    for (const auto& entry : matrix.entries) {
        EXPECT_FALSE(entry.source_layer.name.empty());
        EXPECT_FALSE(entry.notes.empty());
    }
}

}  // namespace
