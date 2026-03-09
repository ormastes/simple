/**
 * @file lr_scheduler.h
 * @brief Learning rate schedulers for LLM training
 *
 * Provides several common learning rate scheduling strategies used in
 * transformer training. A warmup phase followed by cosine decay is the
 * standard schedule for GPT-style models.
 */

#ifndef LR_SCHEDULER_H
#define LR_SCHEDULER_H

namespace llm {

/**
 * @brief Available learning rate scheduler types
 *
 * Each type implements a different decay curve over training steps.
 */
enum class LRSchedulerType {
    Constant,         ///< Fixed learning rate throughout training
    CosineAnnealing,  ///< Cosine decay from initial lr to zero
    WarmupCosine,     ///< Linear warmup followed by cosine decay
    LinearWarmup      ///< Linear warmup followed by constant lr
};

/**
 * @brief Learning rate scheduler configuration and state
 *
 * Computes the learning rate at each training step according to the
 * selected scheduling strategy. Supports warmup phases and multiple
 * decay curves.
 */
struct LRScheduler {
    LRSchedulerType type;   ///< Scheduler type
    float base_lr;          ///< Base (maximum) learning rate
    float min_lr;           ///< Minimum learning rate (floor for decay)
    int warmup_steps;       ///< Number of warmup steps (linear ramp)
    int max_steps;          ///< Total number of training steps

    /**
     * @brief Construct a learning rate scheduler
     *
     * @param type         Scheduler type (default: WarmupCosine)
     * @param base_lr      Base learning rate (default: 1e-4)
     * @param min_lr       Minimum learning rate (default: 1e-6)
     * @param warmup_steps Number of warmup steps (default: 1000)
     * @param max_steps    Total training steps (default: 100000)
     */
    LRScheduler(LRSchedulerType type = LRSchedulerType::WarmupCosine,
                float base_lr = 1e-4f, float min_lr = 1e-6f,
                int warmup_steps = 1000, int max_steps = 100000)
        : type(type), base_lr(base_lr), min_lr(min_lr),
          warmup_steps(warmup_steps), max_steps(max_steps) {}

    /**
     * @brief Get the learning rate for a given training step
     *
     * Computes the learning rate based on the scheduler type:
     * - Constant: returns base_lr
     * - CosineAnnealing: lr * 0.5 * (1 + cos(pi * step / max_steps))
     * - WarmupCosine: linear warmup then cosine decay
     * - LinearWarmup: linear warmup then constant lr
     *
     * @param step Current training step (0-indexed)
     * @return Learning rate for this step
     */
    float get_lr(int step) const;
};

/**
 * @brief Compute cosine annealing learning rate
 *
 * lr = min_lr + 0.5 * (base_lr - min_lr) * (1 + cos(pi * step / max_steps))
 *
 * @param base_lr    Maximum learning rate
 * @param min_lr     Minimum learning rate
 * @param step       Current step
 * @param max_steps  Total training steps
 * @return Decayed learning rate
 */
float cosine_annealing_lr(float base_lr, float min_lr, int step, int max_steps);

/**
 * @brief Compute warmup + cosine decay learning rate
 *
 * During warmup: lr = base_lr * step / warmup_steps
 * After warmup:  cosine annealing from base_lr to min_lr
 *
 * @param base_lr       Maximum learning rate
 * @param min_lr        Minimum learning rate
 * @param step          Current step
 * @param warmup_steps  Number of warmup steps
 * @param max_steps     Total training steps
 * @return Scheduled learning rate
 */
float warmup_cosine_lr(float base_lr, float min_lr, int step, int warmup_steps, int max_steps);

/**
 * @brief Compute linear warmup learning rate
 *
 * During warmup: lr = base_lr * step / warmup_steps
 * After warmup:  lr = base_lr (constant)
 *
 * @param base_lr       Maximum learning rate
 * @param step          Current step
 * @param warmup_steps  Number of warmup steps
 * @return Scheduled learning rate
 */
float linear_warmup_lr(float base_lr, int step, int warmup_steps);

} // namespace llm

#endif // LR_SCHEDULER_H
