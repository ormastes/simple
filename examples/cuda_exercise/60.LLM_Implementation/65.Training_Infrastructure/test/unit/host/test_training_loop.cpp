/**
 * @file test_training_loop.cpp
 * @brief Unit tests for training configuration and loop orchestration
 *
 * Tests the TrainingConfig construction, LRScheduler dispatch, and
 * helper functions for the training pipeline. These are host-side
 * tests that verify configuration correctness without GPU operations.
 */

#include <gtest/gtest.h>
#include "common/training_config.h"
#include "common/lr_scheduler.h"
#include <cmath>

namespace llm {
namespace test {

/**
 * @brief Test suite for TrainingConfig
 */
class TrainingConfigTest : public ::testing::Test {
protected:
    TrainingConfig config;
};

/// Verify default training configuration values match GPT-2 conventions
TEST_F(TrainingConfigTest, DefaultValues) {
    EXPECT_EQ(config.batch_size, 8);
    EXPECT_EQ(config.seq_len, 1024);
    EXPECT_EQ(config.max_steps, 100000);
    EXPECT_FLOAT_EQ(config.lr, 6e-4f);
    EXPECT_FLOAT_EQ(config.weight_decay, 0.1f);
    EXPECT_FLOAT_EQ(config.beta1, 0.9f);
    EXPECT_FLOAT_EQ(config.beta2, 0.95f);
    EXPECT_EQ(config.warmup_steps, 2000);
    EXPECT_EQ(config.lr_schedule, LRSchedulerType::WarmupCosine);
    EXPECT_FLOAT_EQ(config.grad_clip, 1.0f);
    EXPECT_EQ(config.grad_accum_steps, 1);
    EXPECT_EQ(config.eval_interval, 500);
    EXPECT_EQ(config.save_interval, 5000);
    EXPECT_EQ(config.log_interval, 10);
}

/// Verify get_optimizer_config extracts correct AdamW parameters
TEST_F(TrainingConfigTest, GetOptimizerConfig) {
    AdamWConfig opt = config.get_optimizer_config();
    EXPECT_FLOAT_EQ(opt.lr, config.lr);
    EXPECT_FLOAT_EQ(opt.beta1, config.beta1);
    EXPECT_FLOAT_EQ(opt.beta2, config.beta2);
    EXPECT_FLOAT_EQ(opt.weight_decay, config.weight_decay);
}

/// Verify get_lr_scheduler builds correct scheduler
TEST_F(TrainingConfigTest, GetLRScheduler) {
    LRScheduler sched = config.get_lr_scheduler();
    EXPECT_EQ(sched.type, LRSchedulerType::WarmupCosine);
    EXPECT_FLOAT_EQ(sched.base_lr, config.lr);
    EXPECT_EQ(sched.warmup_steps, config.warmup_steps);
    EXPECT_EQ(sched.max_steps, config.max_steps);
}

/**
 * @brief Test suite for LRScheduler
 */
class LRSchedulerTest : public ::testing::Test {};

/// Constant scheduler returns base_lr at every step
TEST_F(LRSchedulerTest, ConstantSchedule) {
    LRScheduler sched(LRSchedulerType::Constant, 1e-3f);
    EXPECT_FLOAT_EQ(sched.get_lr(0), 1e-3f);
    EXPECT_FLOAT_EQ(sched.get_lr(500), 1e-3f);
    EXPECT_FLOAT_EQ(sched.get_lr(99999), 1e-3f);
}

/// CosineAnnealing starts at base_lr and decays toward min_lr
TEST_F(LRSchedulerTest, CosineAnnealingSchedule) {
    float base_lr = 1e-3f;
    float min_lr = 1e-5f;
    LRScheduler sched(LRSchedulerType::CosineAnnealing, base_lr, min_lr, 0, 1000);

    // At step 0: should be close to base_lr
    float lr0 = sched.get_lr(0);
    EXPECT_NEAR(lr0, base_lr, 1e-6f);

    // At step max_steps: should be close to min_lr
    float lr_end = sched.get_lr(1000);
    EXPECT_NEAR(lr_end, min_lr, 1e-6f);

    // At step max_steps/2: should be midpoint
    float lr_mid = sched.get_lr(500);
    float expected_mid = min_lr + 0.5f * (base_lr - min_lr);
    EXPECT_NEAR(lr_mid, expected_mid, 1e-5f);
}

/// WarmupCosine: linear warmup then cosine decay
TEST_F(LRSchedulerTest, WarmupCosineSchedule) {
    float base_lr = 1e-3f;
    float min_lr = 1e-5f;
    int warmup_steps = 100;
    int max_steps = 1000;
    LRScheduler sched(LRSchedulerType::WarmupCosine, base_lr, min_lr, warmup_steps, max_steps);

    // At step 0: lr should be 0 (start of warmup)
    EXPECT_NEAR(sched.get_lr(0), 0.0f, 1e-6f);

    // At step warmup_steps/2: should be half of base_lr
    EXPECT_NEAR(sched.get_lr(50), base_lr * 0.5f, 1e-5f);

    // At step warmup_steps: should be base_lr
    EXPECT_NEAR(sched.get_lr(100), base_lr, 1e-5f);

    // LR should decrease after warmup
    EXPECT_GT(sched.get_lr(100), sched.get_lr(500));
}

/// LinearWarmup: ramp up then constant
TEST_F(LRSchedulerTest, LinearWarmupSchedule) {
    float base_lr = 1e-3f;
    int warmup_steps = 100;
    LRScheduler sched(LRSchedulerType::LinearWarmup, base_lr, 0.0f, warmup_steps, 1000);

    // During warmup: linear ramp
    EXPECT_NEAR(sched.get_lr(0), 0.0f, 1e-6f);
    EXPECT_NEAR(sched.get_lr(50), base_lr * 0.5f, 1e-5f);

    // After warmup: constant
    EXPECT_NEAR(sched.get_lr(100), base_lr, 1e-5f);
    EXPECT_NEAR(sched.get_lr(500), base_lr, 1e-5f);
    EXPECT_NEAR(sched.get_lr(999), base_lr, 1e-5f);
}

/// GRPORewardConfig default values
TEST(GRPORewardConfigTest, DefaultValues) {
    GRPORewardConfig config;
    EXPECT_FLOAT_EQ(config.correctness_weight, 1.0f);
    EXPECT_FLOAT_EQ(config.format_weight, 0.1f);
    EXPECT_FLOAT_EQ(config.length_penalty, 0.001f);
    EXPECT_EQ(config.num_samples, 4);
}

} // namespace test
} // namespace llm
