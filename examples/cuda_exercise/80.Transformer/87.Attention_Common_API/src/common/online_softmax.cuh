/**
 * @file online_softmax.cuh
 * @brief Numerically stable online/streaming softmax computation
 *
 * Implements the online softmax algorithm used in FlashAttention,
 * which computes softmax in a single pass without materializing the full attention matrix.
 */
#pragma once
#include <cuda_runtime.h>
#include <cfloat>

namespace transformer {

/**
 * @brief Online softmax state for incremental computation
 */
struct SoftmaxState {
    float max_val;  ///< Running maximum
    float sum_exp;  ///< Running sum of exp(x - max)

    __device__ __forceinline__ SoftmaxState() : max_val(-FLT_MAX), sum_exp(0.0f) {}
};

/**
 * @brief Update softmax state with a new value
 * @param[in,out] state Current softmax state to update
 * @param[in] val New value to incorporate
 */
__device__ __forceinline__ void online_softmax_update(SoftmaxState& state, float val) {
    float new_max = fmaxf(state.max_val, val);
    float exp_diff = expf(state.max_val - new_max);
    state.sum_exp = state.sum_exp * exp_diff + expf(val - new_max);
    state.max_val = new_max;
}

/**
 * @brief Merge two softmax states (for parallel reduction)
 * @param[in] a First softmax state
 * @param[in] b Second softmax state
 * @return Merged softmax state representing the union of both
 */
__device__ __forceinline__ SoftmaxState online_softmax_merge(SoftmaxState a, SoftmaxState b) {
    SoftmaxState result;
    result.max_val = fmaxf(a.max_val, b.max_val);
    float exp_a = expf(a.max_val - result.max_val);
    float exp_b = expf(b.max_val - result.max_val);
    result.sum_exp = a.sum_exp * exp_a + b.sum_exp * exp_b;
    return result;
}

/**
 * @brief Finalize softmax: compute exp(x - max) / sum for a single value
 * @param[in] val The raw value to normalize
 * @param[in] state The finalized softmax state (max and sum)
 * @return Softmax probability for val
 */
__device__ __forceinline__ float online_softmax_finalize(float val, const SoftmaxState& state) {
    return expf(val - state.max_val) / state.sum_exp;
}

/**
 * @brief Rescale accumulated output when softmax max changes
 *
 * Used in FlashAttention to rescale partial PV products when processing
 * a new key tile that shifts the running maximum.
 *
 * @param[in] old_val Previous accumulated value
 * @param[in] old_max Previous running maximum
 * @param[in] new_max Updated running maximum
 * @param[in] old_sum Previous running sum of exponentials
 * @param[in] new_sum Updated running sum of exponentials
 * @return Rescaled value consistent with the new softmax normalization
 */
__device__ __forceinline__ float online_softmax_rescale(float old_val, float old_max, float new_max, float old_sum, float new_sum) {
    return old_val * (expf(old_max - new_max) * old_sum / new_sum);
}

/**
 * @brief Standard row-wise softmax kernel for a row of length N
 *
 * Three-pass implementation: find max, compute exp and sum, normalize.
 * Used as a reference for validating the online algorithm.
 *
 * @param[in,out] data Row data (modified in-place)
 * @param[in] N Number of elements
 */
__device__ void row_softmax(float* data, int N) {
    // Find max
    float max_val = -FLT_MAX;
    for (int i = 0; i < N; i++) {
        max_val = fmaxf(max_val, data[i]);
    }
    // Compute exp and sum
    float sum = 0.0f;
    for (int i = 0; i < N; i++) {
        data[i] = expf(data[i] - max_val);
        sum += data[i];
    }
    // Normalize
    float inv_sum = 1.0f / sum;
    for (int i = 0; i < N; i++) {
        data[i] *= inv_sum;
    }
}

} // namespace transformer
