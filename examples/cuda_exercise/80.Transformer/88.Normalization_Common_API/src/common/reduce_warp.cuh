/**
 * @file reduce_warp.cuh
 * @brief Warp-level reduction primitives using __shfl_xor_sync
 */
#pragma once
#include <cuda_runtime.h>
#include <cfloat>

namespace transformer {

/**
 * @brief Warp-level sum reduction using butterfly shuffle
 * @param[in] val Value from each lane
 * @return Sum of all values across the warp (all lanes get the result)
 */
__device__ __forceinline__ float warp_reduce_sum(float val) {
    for (int offset = 16; offset > 0; offset >>= 1) {
        val += __shfl_xor_sync(0xffffffff, val, offset);
    }
    return val;
}

/**
 * @brief Warp-level max reduction
 * @param[in] val Value from each lane
 * @return Maximum of all values across the warp (all lanes get the result)
 */
__device__ __forceinline__ float warp_reduce_max(float val) {
    for (int offset = 16; offset > 0; offset >>= 1) {
        val = fmaxf(val, __shfl_xor_sync(0xffffffff, val, offset));
    }
    return val;
}

/**
 * @brief Warp-level min reduction
 * @param[in] val Value from each lane
 * @return Minimum of all values across the warp (all lanes get the result)
 */
__device__ __forceinline__ float warp_reduce_min(float val) {
    for (int offset = 16; offset > 0; offset >>= 1) {
        val = fminf(val, __shfl_xor_sync(0xffffffff, val, offset));
    }
    return val;
}

/**
 * @brief Partial warp sum reduction for first N lanes
 * @tparam WARP_SIZE Warp size (default 32)
 * @param[in] val Value from each lane
 * @param[in] active_lanes Number of active lanes participating in the reduction
 * @return Sum of values from the active lanes
 */
template<int WARP_SIZE = 32>
__device__ __forceinline__ float warp_reduce_sum_partial(float val, int active_lanes) {
    unsigned mask = (active_lanes >= 32) ? 0xffffffff : ((1u << active_lanes) - 1);
    for (int offset = 16; offset > 0; offset >>= 1) {
        val += __shfl_xor_sync(mask, val, offset);
    }
    return val;
}

} // namespace transformer
