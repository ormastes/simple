#include <gtest/gtest.h>

#include "expert_config.h"

namespace {

using attention_expert::ExpertConfig;
using attention_expert::ExpertLoadConfig;
using attention_expert::ExpertNVMeLayout;
using attention_expert::ExpertWeights;

TEST(ExpertConfigTest, DefaultConfigHasBalancedSettings) {
    ExpertConfig config;
    EXPECT_EQ(config.num_experts, 8u);
    EXPECT_EQ(config.experts_per_token, 2u);
    EXPECT_EQ(config.hidden_dim, 512u);
    EXPECT_EQ(config.ffn_dim, 2048u);
    EXPECT_TRUE(config.use_bias);
    EXPECT_FLOAT_EQ(config.capacity_factor, 1.25f);
    EXPECT_TRUE(config.normalize_scores);
}

TEST(ExpertConfigTest, ExpertWeightsInitialPointersNull) {
    ExpertWeights weights;
    EXPECT_EQ(weights.w1, nullptr);
    EXPECT_EQ(weights.w2, nullptr);
    EXPECT_EQ(weights.b1, nullptr);
    EXPECT_EQ(weights.b2, nullptr);
}

TEST(ExpertConfigTest, NvmeLayoutComputesOffsets) {
    ExpertNVMeLayout layout;
    layout.base_offset = 4096;
    layout.stride_bytes = 2048;

    EXPECT_EQ(layout.get_expert_offset(0), 4096u);
    EXPECT_EQ(layout.get_expert_offset(1), 6144u);
    EXPECT_EQ(layout.get_expert_offset(10), 4096u + 10u * 2048u);
}

TEST(ExpertConfigTest, ExpertLoadConfigDefaults) {
    ExpertLoadConfig config;
    EXPECT_FALSE(config.load_on_demand);
    EXPECT_EQ(config.nvme_device_path, nullptr);
    EXPECT_EQ(config.layout.base_offset, 0u);
    EXPECT_EQ(config.expert_cache_ptrs, nullptr);
    EXPECT_EQ(config.expert_loaded, nullptr);
    EXPECT_EQ(config.max_cached_experts, 0u);
    EXPECT_EQ(config.io_buffer, nullptr);
    EXPECT_EQ(config.io_buffer_size, 0u);
}

}  // namespace
