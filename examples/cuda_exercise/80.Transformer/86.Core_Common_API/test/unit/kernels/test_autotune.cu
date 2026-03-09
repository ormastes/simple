/**
 * @file test_autotune.cu
 * @brief Unit tests for autotuning registry
 */
#include <gtest/gtest.h>
#include "common/autotune_registry.cuh"
#include "gpu_gtest.h"

class AutotuneRegistryTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
        transformer::clear_autotune_cache();
    }

    void TearDown() override {
        transformer::clear_autotune_cache();
        GpuTest::TearDown();
    }
};

/**
 * @brief Test default config for SM >= 70 returns WMMA
 */
TEST_F(AutotuneRegistryTest, DefaultConfigSM70) {
    auto config = transformer::get_best_config(256, 256, 256, 75);
    EXPECT_EQ(config.kernel, transformer::GemmKernel::WMMA_FP16);
    EXPECT_EQ(config.tile_m, 16);
    EXPECT_EQ(config.tile_n, 16);
    EXPECT_EQ(config.tile_k, 16);
    EXPECT_EQ(config.M, 256);
    EXPECT_EQ(config.N, 256);
    EXPECT_EQ(config.K, 256);
    EXPECT_EQ(config.sm_version, 75);
}

/**
 * @brief Test default config for SM < 70 returns SIMT
 */
TEST_F(AutotuneRegistryTest, DefaultConfigSM60) {
    auto config = transformer::get_best_config(128, 128, 128, 60);
    EXPECT_EQ(config.kernel, transformer::GemmKernel::SIMT_FP32);
    EXPECT_EQ(config.tile_m, 32);
    EXPECT_EQ(config.tile_n, 32);
    EXPECT_EQ(config.tile_k, 8);
}

/**
 * @brief Test register and retrieve a config
 */
TEST_F(AutotuneRegistryTest, RegisterAndRetrieve) {
    transformer::GemmConfig custom;
    custom.M = 512; custom.N = 512; custom.K = 512;
    custom.kernel = transformer::GemmKernel::INT8_DP4A;
    custom.tile_m = 64; custom.tile_n = 64; custom.tile_k = 32;
    custom.sm_version = 75;

    transformer::register_config(custom);

    auto retrieved = transformer::get_best_config(512, 512, 512, 75);
    EXPECT_EQ(retrieved.kernel, transformer::GemmKernel::INT8_DP4A);
    EXPECT_EQ(retrieved.tile_m, 64);
    EXPECT_EQ(retrieved.tile_n, 64);
    EXPECT_EQ(retrieved.tile_k, 32);
}

/**
 * @brief Test that different problem sizes get independent configs
 */
TEST_F(AutotuneRegistryTest, IndependentConfigs) {
    transformer::GemmConfig config1;
    config1.M = 128; config1.N = 128; config1.K = 128;
    config1.kernel = transformer::GemmKernel::SIMT_FP32;
    config1.tile_m = 32; config1.tile_n = 32; config1.tile_k = 8;
    config1.sm_version = 75;

    transformer::GemmConfig config2;
    config2.M = 256; config2.N = 256; config2.K = 256;
    config2.kernel = transformer::GemmKernel::WMMA_FP16;
    config2.tile_m = 16; config2.tile_n = 16; config2.tile_k = 16;
    config2.sm_version = 75;

    transformer::register_config(config1);
    transformer::register_config(config2);

    auto r1 = transformer::get_best_config(128, 128, 128, 75);
    auto r2 = transformer::get_best_config(256, 256, 256, 75);

    EXPECT_EQ(r1.kernel, transformer::GemmKernel::SIMT_FP32);
    EXPECT_EQ(r2.kernel, transformer::GemmKernel::WMMA_FP16);
}

/**
 * @brief Test clear cache resets to defaults
 */
TEST_F(AutotuneRegistryTest, ClearCache) {
    transformer::GemmConfig custom;
    custom.M = 64; custom.N = 64; custom.K = 64;
    custom.kernel = transformer::GemmKernel::INT8_DP4A;
    custom.tile_m = 8; custom.tile_n = 8; custom.tile_k = 4;
    custom.sm_version = 75;

    transformer::register_config(custom);

    // Verify it was registered
    auto before = transformer::get_best_config(64, 64, 64, 75);
    EXPECT_EQ(before.kernel, transformer::GemmKernel::INT8_DP4A);

    // Clear and verify default
    transformer::clear_autotune_cache();
    auto after = transformer::get_best_config(64, 64, 64, 75);
    EXPECT_EQ(after.kernel, transformer::GemmKernel::WMMA_FP16);
}

/**
 * @brief Test that overwriting a config works
 */
TEST_F(AutotuneRegistryTest, OverwriteConfig) {
    transformer::GemmConfig v1;
    v1.M = 128; v1.N = 128; v1.K = 128;
    v1.kernel = transformer::GemmKernel::SIMT_FP32;
    v1.tile_m = 32; v1.tile_n = 32; v1.tile_k = 8;
    v1.sm_version = 80;

    transformer::register_config(v1);
    auto r1 = transformer::get_best_config(128, 128, 128, 80);
    EXPECT_EQ(r1.kernel, transformer::GemmKernel::SIMT_FP32);

    // Overwrite with WMMA
    transformer::GemmConfig v2 = v1;
    v2.kernel = transformer::GemmKernel::WMMA_FP16;
    v2.tile_m = 16; v2.tile_n = 16; v2.tile_k = 16;
    transformer::register_config(v2);

    auto r2 = transformer::get_best_config(128, 128, 128, 80);
    EXPECT_EQ(r2.kernel, transformer::GemmKernel::WMMA_FP16);
    EXPECT_EQ(r2.tile_m, 16);
}
