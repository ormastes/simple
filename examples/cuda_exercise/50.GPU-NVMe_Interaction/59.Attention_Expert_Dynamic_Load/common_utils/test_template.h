/**
 * @file test_template.h
 * @brief GoogleTest template utilities for Module 59
 */

#pragma once

#include <gtest/gtest.h>
#include <string>

namespace module59 {
namespace test {

/**
 * @brief Base test fixture for Module 59 data structure tests
 * @tparam DataType The data structure type to test
 */
template<typename DataType>
class Module59TestFixture : public ::testing::Test {
protected:
    DataType data;

    void SetUp() override {
        // Build the data using the appropriate builder function
        // This will be specialized per module
    }

    /**
     * @brief Test that the collection has the expected minimum count
     * @param expected_min Expected minimum count
     */
    void TestMinimumCount(std::size_t expected_min) {
        EXPECT_GE(data.entries.size(), expected_min)
            << "Collection should have at least " << expected_min << " entries";
    }

    /**
     * @brief Test that all entries have valid (non-empty) names
     */
    void TestValidNames() {
        for (const auto& entry : data.entries) {
            EXPECT_FALSE(entry.name.empty())
                << "Entry name should not be empty";
        }
    }

    /**
     * @brief Test that all entries have valid descriptions
     */
    void TestValidDescriptions() {
        for (const auto& entry : data.entries) {
            if constexpr (requires { entry.description; }) {
                EXPECT_FALSE(entry.description.empty())
                    << "Entry description should not be empty for: " << entry.name;
            }
        }
    }
};

/**
 * @brief Macro to quickly generate standard tests for Module 59 data structures
 */
#define GENERATE_MODULE59_TESTS(TestName, DataType, BuildFunc, MinCount) \
class TestName : public module59::test::Module59TestFixture<DataType> { \
protected: \
    void SetUp() override { \
        this->data = BuildFunc(); \
    } \
}; \
\
TEST_F(TestName, ContainsExpectedCount) { \
    TestMinimumCount(MinCount); \
} \
\
TEST_F(TestName, ValidateStructure) { \
    TestValidNames(); \
    TestValidDescriptions(); \
}

} // namespace test
} // namespace module59