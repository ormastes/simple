/**
 * @file training_config.h
 * @brief Training configuration for LLM training pipelines
 *
 * Defines the TrainingConfig struct that holds all hyperparameters
 * for a training run, including batch size, learning rate schedule,
 * gradient clipping, and evaluation intervals.
 */

#ifndef TRAINING_CONFIG_H
#define TRAINING_CONFIG_H

#include "optimizer.h"
#include "lr_scheduler.h"

namespace llm {

/**
 * @brief Complete training configuration
 *
 * Aggregates all training hyperparameters into a single structure
 * for convenient initialization and serialization. Covers the full
 * training pipeline from data loading through optimizer settings.
 */
struct TrainingConfig {
    // Data and batching
    int batch_size;       ///< Number of sequences per training batch
    int seq_len;          ///< Sequence length (context window)
    int max_steps;        ///< Maximum number of training steps

    // Optimizer
    float lr;             ///< Peak learning rate
    float weight_decay;   ///< AdamW weight decay coefficient
    float beta1;          ///< AdamW first moment decay
    float beta2;          ///< AdamW second moment decay

    // Learning rate schedule
    int warmup_steps;     ///< Number of linear warmup steps
    LRSchedulerType lr_schedule;  ///< Learning rate schedule type

    // Gradient handling
    float grad_clip;      ///< Maximum gradient norm (0 = no clipping)
    int grad_accum_steps; ///< Gradient accumulation steps (effective batch multiplier)

    // Evaluation
    int eval_interval;    ///< Steps between validation evaluations
    int save_interval;    ///< Steps between checkpoint saves
    int log_interval;     ///< Steps between logging

    /**
     * @brief Construct training config with default GPT-2 training values
     */
    TrainingConfig()
        : batch_size(8), seq_len(1024), max_steps(100000),
          lr(6e-4f), weight_decay(0.1f), beta1(0.9f), beta2(0.95f),
          warmup_steps(2000), lr_schedule(LRSchedulerType::WarmupCosine),
          grad_clip(1.0f), grad_accum_steps(1),
          eval_interval(500), save_interval(5000), log_interval(10) {}

    /**
     * @brief Build an AdamWConfig from training parameters
     * @return AdamWConfig with lr, beta1, beta2, weight_decay from this config
     */
    AdamWConfig get_optimizer_config() const {
        return AdamWConfig(lr, beta1, beta2, weight_decay);
    }

    /**
     * @brief Build an LRScheduler from training parameters
     * @return LRScheduler configured from this training config
     */
    LRScheduler get_lr_scheduler() const {
        return LRScheduler(lr_schedule, lr, 1e-6f, warmup_steps, max_steps);
    }
};

/**
 * @brief GRPO (Group Relative Policy Optimization) reward configuration
 *
 * Configuration for reasoning-focused training using GRPO, where
 * the model is rewarded for producing correct chain-of-thought reasoning.
 * This is a placeholder for DeepSeek R1-style training.
 */
struct GRPORewardConfig {
    float correctness_weight;  ///< Weight for answer correctness reward
    float format_weight;       ///< Weight for output format compliance reward
    float length_penalty;      ///< Penalty coefficient for excessive output length
    int num_samples;           ///< Number of samples per prompt for group scoring

    /**
     * @brief Construct GRPO reward config with default values
     */
    GRPORewardConfig()
        : correctness_weight(1.0f), format_weight(0.1f),
          length_penalty(0.001f), num_samples(4) {}
};

} // namespace llm

#endif // TRAINING_CONFIG_H
