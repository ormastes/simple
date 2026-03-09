/**
 * @file reduce_block.cuh
 * @brief Block-level reduction using shared memory and warp primitives
 */
#pragma once
#include <cuda_runtime.h>
#include "reduce_warp.cuh"

namespace transformer {

/**
 * @brief Block-level sum reduction
 * Uses shared memory for inter-warp communication and warp shuffles within warps.
 *
 * @param[in] val Value from each thread
 * @param[in,out] smem Shared memory buffer (must hold at least blockDim.x/32 floats)
 * @return Sum of all values in the block (broadcast to all threads)
 */
__device__ __forceinline__ float block_reduce_sum(float val, float* smem) {
    int lane = threadIdx.x % 32;
    int warp_id = threadIdx.x / 32;
    int num_warps = (blockDim.x + 31) / 32;

    // First reduce within each warp
    val = warp_reduce_sum(val);

    // Write warp results to shared memory
    if (lane == 0) {
        smem[warp_id] = val;
    }
    __syncthreads();

    // First warp reduces across warps
    if (warp_id == 0) {
        val = (lane < num_warps) ? smem[lane] : 0.0f;
        val = warp_reduce_sum(val);
    }
    __syncthreads();

    // Broadcast result to all threads via shared memory
    if (threadIdx.x == 0) {
        smem[0] = val;
    }
    __syncthreads();

    return smem[0];
}

/**
 * @brief Block-level max reduction
 * Uses shared memory for inter-warp communication and warp shuffles within warps.
 *
 * @param[in] val Value from each thread
 * @param[in,out] smem Shared memory buffer (must hold at least blockDim.x/32 floats)
 * @return Maximum of all values in the block (broadcast to all threads)
 */
__device__ __forceinline__ float block_reduce_max(float val, float* smem) {
    int lane = threadIdx.x % 32;
    int warp_id = threadIdx.x / 32;
    int num_warps = (blockDim.x + 31) / 32;

    val = warp_reduce_max(val);

    if (lane == 0) {
        smem[warp_id] = val;
    }
    __syncthreads();

    if (warp_id == 0) {
        val = (lane < num_warps) ? smem[lane] : -FLT_MAX;
        val = warp_reduce_max(val);
    }
    __syncthreads();

    if (threadIdx.x == 0) {
        smem[0] = val;
    }
    __syncthreads();

    return smem[0];
}

} // namespace transformer
