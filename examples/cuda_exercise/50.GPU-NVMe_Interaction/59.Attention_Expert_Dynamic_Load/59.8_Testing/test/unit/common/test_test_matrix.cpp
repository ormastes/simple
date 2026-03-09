#include <gtest/gtest.h>

#include "test_matrix.h"

namespace {

using testing59::buildTestMatrix;

TEST(TestMatrixTest, ContainsUnitAndIntegrationEntries) {
    const auto matrix = buildTestMatrix();
    bool found_unit = false;
    bool found_integration = false;
    for (const auto& entry : matrix.entries) {
        if (entry.type == "Unit") {
            found_unit = true;
        }
        if (entry.type == "Integration") {
            found_integration = true;
        }
    }
    EXPECT_TRUE(found_unit);
    EXPECT_TRUE(found_integration);
}

TEST(TestMatrixTest, TestCountAtLeastThree) {
    const auto matrix = buildTestMatrix();
    EXPECT_GE(matrix.testCount(), 3u);
}

}  // namespace
