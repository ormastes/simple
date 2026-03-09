#include <gtest/gtest.h>

#include "dispatcher_checks.h"

namespace {

using torch59::buildDispatcherMatrix;

TEST(DispatcherMatrixTest, ContainsAutogradEntry) {
    const auto matrix = buildDispatcherMatrix();
    bool found_autograd = false;
    for (const auto& check : matrix.checks) {
        if (check.dispatch_key.find("Autograd") != std::string::npos) {
            found_autograd = true;
        }
    }
    EXPECT_TRUE(found_autograd);
}

TEST(DispatcherMatrixTest, CheckCountMatchesExpectations) {
    const auto matrix = buildDispatcherMatrix();
    EXPECT_GE(matrix.checkCount(), 4u);
}

}  // namespace
