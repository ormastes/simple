/**
 * @file vector_io.cuh
 * @brief Vectorized load/store templates for GPU memory operations
 *
 * Provides type-safe vectorized memory access using float2, float4, and half2
 * for improved memory bandwidth utilization.
 */
#pragma once

#include <cuda_runtime.h>
#include <cuda_fp16.h>
#include <cstdint>

namespace transformer {

/**
 * @brief Vectorized load of 4 floats from global memory
 * @param[in] addr Aligned source address (must be 16-byte aligned)
 * @return float4 containing 4 loaded values
 */
__device__ __forceinline__ float4 load_float4(const float* addr) {
    return *reinterpret_cast<const float4*>(addr);
}

/**
 * @brief Vectorized store of 4 floats to global memory
 * @param[out] addr Aligned destination address (must be 16-byte aligned)
 * @param[in] val float4 value to store
 */
__device__ __forceinline__ void store_float4(float* addr, float4 val) {
    *reinterpret_cast<float4*>(addr) = val;
}

/**
 * @brief Vectorized load of 2 floats from global memory
 * @param[in] addr Aligned source address (must be 8-byte aligned)
 * @return float2 containing 2 loaded values
 */
__device__ __forceinline__ float2 load_float2(const float* addr) {
    return *reinterpret_cast<const float2*>(addr);
}

/**
 * @brief Vectorized store of 2 floats to global memory
 * @param[out] addr Aligned destination address (must be 8-byte aligned)
 * @param[in] val float2 value to store
 */
__device__ __forceinline__ void store_float2(float* addr, float2 val) {
    *reinterpret_cast<float2*>(addr) = val;
}

/**
 * @brief Vectorized load of 2 half-precision values
 * @param[in] addr Aligned source address (must be 4-byte aligned)
 * @return half2 containing 2 loaded values
 */
__device__ __forceinline__ half2 load_half2(const half* addr) {
    return *reinterpret_cast<const half2*>(addr);
}

/**
 * @brief Vectorized store of 2 half-precision values
 * @param[out] addr Aligned destination address (must be 4-byte aligned)
 * @param[in] val half2 value to store
 */
__device__ __forceinline__ void store_half2(half* addr, half2 val) {
    *reinterpret_cast<half2*>(addr) = val;
}

/**
 * @brief Check if address is aligned to N bytes
 * @tparam N Alignment requirement in bytes
 * @param[in] ptr Pointer to check
 * @return true if address is aligned to N bytes
 */
template<int N>
__device__ __forceinline__ bool is_aligned(const void* ptr) {
    return (reinterpret_cast<uintptr_t>(ptr) % N) == 0;
}

/**
 * @brief Safe vectorized load with fallback for unaligned access
 *
 * Attempts a 16-byte aligned float4 load. If the source address is not
 * properly aligned, falls back to four individual scalar loads.
 *
 * @param[out] dst Destination array (4 floats)
 * @param[in] src Source pointer in global memory
 */
__device__ __forceinline__ void safe_load_float4(float* dst, const float* src) {
    if (is_aligned<16>(src)) {
        float4 v = load_float4(src);
        dst[0] = v.x; dst[1] = v.y; dst[2] = v.z; dst[3] = v.w;
    } else {
        dst[0] = src[0]; dst[1] = src[1]; dst[2] = src[2]; dst[3] = src[3];
    }
}

/**
 * @brief Copy N elements using vectorized loads/stores where possible
 *
 * Uses float4 (128-bit) vectorized operations when both source and destination
 * are 16-byte aligned and VEC_SIZE is 4. Falls back to scalar copies for
 * remaining elements or unaligned addresses.
 *
 * @tparam VEC_SIZE Vector width for aligned copies (default: 4)
 * @param[out] dst Destination pointer
 * @param[in] src Source pointer
 * @param[in] n Number of float elements to copy
 */
template<int VEC_SIZE = 4>
__device__ void vectorized_copy(float* dst, const float* src, int n) {
    int i = 0;
    if (VEC_SIZE == 4 && is_aligned<16>(src) && is_aligned<16>(dst)) {
        for (; i + 3 < n; i += 4) {
            store_float4(dst + i, load_float4(src + i));
        }
    }
    for (; i < n; i++) {
        dst[i] = src[i];
    }
}

} // namespace transformer
