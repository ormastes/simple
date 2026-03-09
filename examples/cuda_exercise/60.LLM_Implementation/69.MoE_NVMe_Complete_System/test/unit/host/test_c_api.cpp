/**
 * @file test_c_api.cpp
 * @brief Unit tests for the LLM C API lifecycle
 *
 * Tests the create/generate/destroy flow of the C API, including
 * error handling for invalid parameters and model queries.
 */

#include <gtest/gtest.h>
#include "common/llm_api.h"
#include <cstdio>
#include <cstring>
#include <string>

/// Test fixture for C API tests
class LLMCApiTest : public ::testing::Test {
protected:
    /// Temporary config file path
    std::string config_path;

    void SetUp() override {
        // Create a minimal config file
        config_path = "/tmp/test_llm_config.txt";
        FILE* f = fopen(config_path.c_str(), "w");
        ASSERT_NE(f, nullptr);
        fprintf(f, "vocab_size=1000\n");
        fprintf(f, "max_seq_len=128\n");
        fprintf(f, "d_model=64\n");
        fprintf(f, "num_layers=2\n");
        fprintf(f, "num_experts=4\n");
        fclose(f);
    }

    void TearDown() override {
        remove(config_path.c_str());
    }
};

/// Test that a model can be created and destroyed without errors
TEST_F(LLMCApiTest, CreateAndDestroy) {
    LLMModel model = llm_create_model(config_path.c_str());
    ASSERT_NE(model, nullptr);
    llm_destroy_model(model);
}

/// Test that destroying a NULL model is safe
TEST_F(LLMCApiTest, DestroyNull) {
    llm_destroy_model(nullptr);  // Should not crash
}

/// Test that creating a model with NULL path returns NULL
TEST_F(LLMCApiTest, CreateNullPath) {
    LLMModel model = llm_create_model(nullptr);
    EXPECT_EQ(model, nullptr);
}

/// Test model info queries return configured values
TEST_F(LLMCApiTest, ModelInfo) {
    LLMModel model = llm_create_model(config_path.c_str());
    ASSERT_NE(model, nullptr);

    EXPECT_EQ(llm_get_vocab_size(model), 1000);
    EXPECT_EQ(llm_get_max_seq_len(model), 128);
    EXPECT_GT(llm_get_num_parameters(model), 0);

    llm_destroy_model(model);
}

/// Test that model info queries on NULL return -1
TEST_F(LLMCApiTest, ModelInfoNull) {
    EXPECT_EQ(llm_get_vocab_size(nullptr), -1);
    EXPECT_EQ(llm_get_max_seq_len(nullptr), -1);
    EXPECT_EQ(llm_get_num_parameters(nullptr), -1);
}

/// Test basic text generation
TEST_F(LLMCApiTest, GenerateBasic) {
    LLMModel model = llm_create_model(config_path.c_str());
    ASSERT_NE(model, nullptr);

    int input_ids[] = {1, 2, 3, 4, 5};
    int output_ids[10] = {0};
    int generated = llm_generate(model, input_ids, 5, output_ids, 10);

    EXPECT_GT(generated, 0);
    EXPECT_LE(generated, 10);

    llm_destroy_model(model);
}

/// Test generation with invalid parameters returns -1
TEST_F(LLMCApiTest, GenerateInvalid) {
    LLMModel model = llm_create_model(config_path.c_str());
    ASSERT_NE(model, nullptr);

    int buf[10];
    // NULL model
    EXPECT_EQ(llm_generate(nullptr, buf, 5, buf, 10), -1);
    // NULL input
    EXPECT_EQ(llm_generate(model, nullptr, 5, buf, 10), -1);
    // NULL output
    EXPECT_EQ(llm_generate(model, buf, 5, nullptr, 10), -1);
    // Zero input length
    EXPECT_EQ(llm_generate(model, buf, 0, buf, 10), -1);
    // Zero output length
    EXPECT_EQ(llm_generate(model, buf, 5, buf, 0), -1);

    llm_destroy_model(model);
}

/// Test model creation with nonexistent config uses defaults
TEST_F(LLMCApiTest, CreateNonexistentConfig) {
    LLMModel model = llm_create_model("/tmp/nonexistent_config_69.txt");
    ASSERT_NE(model, nullptr);

    // Should use default values
    EXPECT_EQ(llm_get_vocab_size(model), 50257);
    EXPECT_EQ(llm_get_max_seq_len(model), 1024);

    llm_destroy_model(model);
}
