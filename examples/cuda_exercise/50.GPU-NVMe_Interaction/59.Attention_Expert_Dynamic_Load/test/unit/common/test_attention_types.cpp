#include <gtest/gtest.h>

#include "attention_types.h"

namespace {

using attention_expert::AttentionGradients;
using attention_expert::AttentionOutput;
using attention_expert::AttentionWeights;
using attention_expert::NVMeLoadConfig;
using attention_expert::LoadMode;

TEST(AttentionTypesTest, DefaultWeightsPointersNull) {
    AttentionWeights weights;
    EXPECT_EQ(weights.q_weight, nullptr);
    EXPECT_EQ(weights.k_weight, nullptr);
    EXPECT_EQ(weights.v_weight, nullptr);
    EXPECT_EQ(weights.o_weight, nullptr);
    EXPECT_EQ(weights.q_bias, nullptr);
    EXPECT_EQ(weights.k_bias, nullptr);
    EXPECT_EQ(weights.v_bias, nullptr);
    EXPECT_EQ(weights.o_bias, nullptr);
}

TEST(AttentionTypesTest, DefaultOutputPointersNull) {
    AttentionOutput output;
    EXPECT_EQ(output.output, nullptr);
    EXPECT_EQ(output.attention_scores, nullptr);
}

TEST(AttentionTypesTest, DefaultGradientsPointersNull) {
    AttentionGradients grads;
    EXPECT_EQ(grads.grad_input, nullptr);
    EXPECT_EQ(grads.grad_q_weight, nullptr);
    EXPECT_EQ(grads.grad_k_weight, nullptr);
    EXPECT_EQ(grads.grad_v_weight, nullptr);
    EXPECT_EQ(grads.grad_o_weight, nullptr);
    EXPECT_EQ(grads.grad_q_bias, nullptr);
    EXPECT_EQ(grads.grad_k_bias, nullptr);
    EXPECT_EQ(grads.grad_v_bias, nullptr);
    EXPECT_EQ(grads.grad_o_bias, nullptr);
}

TEST(AttentionTypesTest, NvmeLoadConfigDefaultsMatchAllInMemory) {
    NVMeLoadConfig config;
    EXPECT_EQ(config.mode, LoadMode::ALL_IN_MEMORY);
    EXPECT_EQ(config.nvme_path, nullptr);
    EXPECT_EQ(config.weight_offset, 0u);
    EXPECT_EQ(config.weight_size_bytes, 0u);
    EXPECT_EQ(config.staging_buffer, nullptr);
    EXPECT_TRUE(config.use_pinned_memory);
}

TEST(AttentionTypesTest, NvmeLoadConfigCanToggleMode) {
    NVMeLoadConfig config;
    config.mode = LoadMode::DYNAMIC_ALL;
    config.use_pinned_memory = false;

    EXPECT_EQ(config.mode, LoadMode::DYNAMIC_ALL);
    EXPECT_FALSE(config.use_pinned_memory);
}

}  // namespace
