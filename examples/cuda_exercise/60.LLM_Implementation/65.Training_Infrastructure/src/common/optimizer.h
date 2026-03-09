/**
 * @file optimizer.h
 * @brief AdamW optimizer interface for LLM training
 *
 * Provides the AdamW optimizer with decoupled weight decay as described in
 * "Decoupled Weight Decay Regularization" (Loshchilov & Hutter, 2019).
 * AdamW is the standard optimizer for training large language models.
 */

#ifndef OPTIMIZER_H
#define OPTIMIZER_H

#include <cuda_runtime.h>
#include <cstddef>

namespace llm {

/**
 * @brief Configuration for the AdamW optimizer
 *
 * Holds all hyperparameters for the AdamW update rule. Default values
 * follow common practice for transformer training (GPT-style models).
 */
struct AdamWConfig {
    float lr;            ///< Learning rate (step size)
    float beta1;         ///< Exponential decay rate for first moment estimate
    float beta2;         ///< Exponential decay rate for second moment estimate
    float weight_decay;  ///< Decoupled weight decay coefficient
    float eps;           ///< Small constant for numerical stability in denominator

    /**
     * @brief Construct AdamW configuration with default GPT training values
     *
     * @param lr           Learning rate (default: 1e-4)
     * @param beta1        First moment decay (default: 0.9)
     * @param beta2        Second moment decay (default: 0.999)
     * @param weight_decay Weight decay coefficient (default: 0.01)
     * @param eps          Epsilon for stability (default: 1e-8)
     */
    AdamWConfig(float lr = 1e-4f, float beta1 = 0.9f, float beta2 = 0.999f,
                float weight_decay = 0.01f, float eps = 1e-8f)
        : lr(lr), beta1(beta1), beta2(beta2),
          weight_decay(weight_decay), eps(eps) {}
};

/**
 * @brief Optimizer state for AdamW (per-parameter group)
 *
 * Maintains first and second moment buffers and the optimization step
 * counter for bias correction. Each parameter tensor requires its own
 * AdamWState instance.
 */
struct AdamWState {
    float* d_m;    ///< First moment buffer (device) [num_params]
    float* d_v;    ///< Second moment buffer (device) [num_params]
    int step;      ///< Current optimization step (for bias correction)
    size_t size;   ///< Number of parameters in this group
};

/**
 * @brief Perform a single AdamW optimization step on GPU
 *
 * Updates parameters in-place using the AdamW update rule with
 * bias-corrected moment estimates and decoupled weight decay:
 *
 *   m = beta1 * m + (1 - beta1) * grad
 *   v = beta2 * v + (1 - beta2) * grad^2
 *   m_hat = m / (1 - beta1^t)
 *   v_hat = v / (1 - beta2^t)
 *   param = param - lr * (m_hat / (sqrt(v_hat) + eps) + weight_decay * param)
 *
 * @param[in,out] d_params  Model parameters (device) [num_params]
 * @param[in]     d_grads   Parameter gradients (device) [num_params]
 * @param[in,out] state     Optimizer state (moments and step counter)
 * @param[in]     config    Optimizer hyperparameters
 * @param[in]     stream    CUDA stream for async execution (default: 0)
 *
 * @note All device pointers must be pre-allocated
 * @note state.step is incremented after the update
 */
void adamw_step(float* d_params, const float* d_grads,
                AdamWState& state, const AdamWConfig& config,
                cudaStream_t stream = 0);

/**
 * @brief Allocate optimizer state buffers on GPU
 *
 * Allocates first and second moment buffers, initializes them to zero,
 * and sets the step counter to zero.
 *
 * @param num_params Number of parameters in the parameter group
 * @return Allocated AdamWState with zero-initialized moments
 */
AdamWState allocate_adamw_state(size_t num_params);

/**
 * @brief Free optimizer state buffers
 *
 * Releases device memory for moment buffers and resets pointers to nullptr.
 *
 * @param state State to free; pointers set to nullptr after freeing
 */
void free_adamw_state(AdamWState& state);

} // namespace llm

#endif // OPTIMIZER_H
