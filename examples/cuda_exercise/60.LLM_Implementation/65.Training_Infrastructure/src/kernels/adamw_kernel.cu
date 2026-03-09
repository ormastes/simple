/**
 * @file adamw_kernel.cu
 * @brief CUDA kernel for AdamW optimizer parameter update
 *
 * Implements the fused AdamW update rule on GPU, performing moment
 * estimation, bias correction, and parameter update in a single kernel
 * launch for maximum throughput.
 */

#include "common/optimizer.h"
#include <cuda_runtime.h>
#include <cmath>

namespace llm {

/**
 * @brief Fused AdamW update kernel
 *
 * Each thread updates one parameter element. The kernel performs:
 *   m[i] = beta1 * m[i] + (1 - beta1) * grad[i]
 *   v[i] = beta2 * v[i] + (1 - beta2) * grad[i]^2
 *   m_hat = m[i] / (1 - beta1^t)
 *   v_hat = v[i] / (1 - beta2^t)
 *   param[i] -= lr * (m_hat / (sqrt(v_hat) + eps) + weight_decay * param[i])
 *
 * @param[in,out] params       Model parameters [n]
 * @param[in]     grads        Gradients [n]
 * @param[in,out] m            First moment estimates [n]
 * @param[in,out] v            Second moment estimates [n]
 * @param[in]     lr           Current learning rate
 * @param[in]     beta1        First moment decay rate
 * @param[in]     beta2        Second moment decay rate
 * @param[in]     weight_decay Weight decay coefficient
 * @param[in]     eps          Numerical stability constant
 * @param[in]     beta1_power  beta1^step (precomputed for bias correction)
 * @param[in]     beta2_power  beta2^step (precomputed for bias correction)
 * @param[in]     n            Number of parameters
 */
__global__ void adamw_update_kernel(
    float* params, const float* grads,
    float* m, float* v,
    float lr, float beta1, float beta2,
    float weight_decay, float eps,
    float beta1_power, float beta2_power,
    int n
) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= n) return;

    float grad = grads[idx];
    float param = params[idx];

    // Update biased first moment estimate
    float m_new = beta1 * m[idx] + (1.0f - beta1) * grad;
    m[idx] = m_new;

    // Update biased second moment estimate
    float v_new = beta2 * v[idx] + (1.0f - beta2) * grad * grad;
    v[idx] = v_new;

    // Bias-corrected moment estimates
    float m_hat = m_new / (1.0f - beta1_power);
    float v_hat = v_new / (1.0f - beta2_power);

    // AdamW update: decoupled weight decay applied directly to param
    param -= lr * (m_hat / (sqrtf(v_hat) + eps) + weight_decay * param);

    params[idx] = param;
}

/**
 * @brief Perform a single AdamW optimization step on GPU
 *
 * Launches the fused AdamW kernel to update all parameters in one pass.
 * Precomputes beta1^t and beta2^t for bias correction, then increments
 * the step counter.
 *
 * @param[in,out] d_params  Model parameters (device)
 * @param[in]     d_grads   Gradients (device)
 * @param[in,out] state     Optimizer state (moments + step counter)
 * @param[in]     config    AdamW hyperparameters
 * @param[in]     stream    CUDA stream for async execution
 */
void adamw_step(float* d_params, const float* d_grads,
                AdamWState& state, const AdamWConfig& config,
                cudaStream_t stream) {
    // Increment step before computing bias correction
    state.step++;

    // Precompute bias correction terms: beta^step
    float beta1_power = std::pow(config.beta1, static_cast<float>(state.step));
    float beta2_power = std::pow(config.beta2, static_cast<float>(state.step));

    // Launch kernel
    int n = static_cast<int>(state.size);
    int block_size = 256;
    int grid_size = (n + block_size - 1) / block_size;

    adamw_update_kernel<<<grid_size, block_size, 0, stream>>>(
        d_params, d_grads,
        state.d_m, state.d_v,
        config.lr, config.beta1, config.beta2,
        config.weight_decay, config.eps,
        beta1_power, beta2_power,
        n
    );
}

} // namespace llm
