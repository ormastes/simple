/**
 * @file lr_scheduler.cpp
 * @brief Learning rate scheduler implementations
 *
 * Implements several learning rate scheduling strategies commonly used
 * in LLM training. The warmup + cosine decay schedule is the standard
 * choice for GPT-style model training.
 */

#include "common/lr_scheduler.h"
#include <cmath>
#include <algorithm>

#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

namespace llm {

/**
 * @brief Compute cosine annealing learning rate
 *
 * Decays the learning rate from base_lr to min_lr following a cosine curve:
 *   lr = min_lr + 0.5 * (base_lr - min_lr) * (1 + cos(pi * step / max_steps))
 *
 * At step 0 the rate equals base_lr; at max_steps it equals min_lr.
 *
 * @param base_lr    Maximum (initial) learning rate
 * @param min_lr     Minimum (final) learning rate
 * @param step       Current training step
 * @param max_steps  Total number of training steps
 * @return Decayed learning rate for the given step
 */
float cosine_annealing_lr(float base_lr, float min_lr, int step, int max_steps) {
    if (max_steps <= 0) return base_lr;
    float progress = static_cast<float>(step) / static_cast<float>(max_steps);
    progress = std::min(progress, 1.0f);
    return min_lr + 0.5f * (base_lr - min_lr) * (1.0f + std::cos(static_cast<float>(M_PI) * progress));
}

/**
 * @brief Compute warmup + cosine decay learning rate
 *
 * Two-phase schedule:
 * - Phase 1 (step < warmup_steps): Linear warmup from 0 to base_lr
 * - Phase 2 (step >= warmup_steps): Cosine decay from base_lr to min_lr
 *
 * This is the standard schedule for GPT training runs.
 *
 * @param base_lr       Peak learning rate
 * @param min_lr        Floor learning rate
 * @param step          Current training step
 * @param warmup_steps  Number of linear warmup steps
 * @param max_steps     Total training steps (including warmup)
 * @return Scheduled learning rate
 */
float warmup_cosine_lr(float base_lr, float min_lr, int step, int warmup_steps, int max_steps) {
    if (step < warmup_steps) {
        // Linear warmup: ramp from 0 to base_lr
        return base_lr * static_cast<float>(step) / static_cast<float>(std::max(warmup_steps, 1));
    }

    // Cosine decay phase
    int decay_steps = max_steps - warmup_steps;
    int decay_step = step - warmup_steps;
    return cosine_annealing_lr(base_lr, min_lr, decay_step, decay_steps);
}

/**
 * @brief Compute linear warmup learning rate
 *
 * Two-phase schedule:
 * - Phase 1 (step < warmup_steps): Linear ramp from 0 to base_lr
 * - Phase 2 (step >= warmup_steps): Constant at base_lr
 *
 * @param base_lr       Peak / constant learning rate
 * @param step          Current training step
 * @param warmup_steps  Number of warmup steps
 * @return Scheduled learning rate
 */
float linear_warmup_lr(float base_lr, int step, int warmup_steps) {
    if (step < warmup_steps) {
        return base_lr * static_cast<float>(step) / static_cast<float>(std::max(warmup_steps, 1));
    }
    return base_lr;
}

/**
 * @brief LRScheduler::get_lr - dispatch to the appropriate schedule function
 */
float LRScheduler::get_lr(int step) const {
    switch (type) {
        case LRSchedulerType::Constant:
            return base_lr;
        case LRSchedulerType::CosineAnnealing:
            return cosine_annealing_lr(base_lr, min_lr, step, max_steps);
        case LRSchedulerType::WarmupCosine:
            return warmup_cosine_lr(base_lr, min_lr, step, warmup_steps, max_steps);
        case LRSchedulerType::LinearWarmup:
            return linear_warmup_lr(base_lr, step, warmup_steps);
        default:
            return base_lr;
    }
}

} // namespace llm
