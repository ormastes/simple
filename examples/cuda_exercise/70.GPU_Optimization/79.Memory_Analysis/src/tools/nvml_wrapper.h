/**
 * @file nvml_wrapper.h
 * @brief Conditional NVML wrapper for GPU device monitoring.
 */

#pragma once
#include <cstddef>

namespace opt79 {

/**
 * @brief GPU device information queried from NVML or CUDA runtime.
 *
 * When HAS_NVML is defined, provides full GPU metrics (utilization, temperature).
 * Otherwise falls back to CUDA runtime for memory info only.
 */
struct GpuDeviceInfo {
    size_t memory_total;      ///< Total GPU memory in bytes
    size_t memory_used;       ///< Used GPU memory in bytes
    size_t memory_free;       ///< Free GPU memory in bytes
    unsigned int gpu_util;    ///< GPU utilization percentage (0-100)
    unsigned int mem_util;    ///< Memory utilization percentage (0-100)
    unsigned int temperature; ///< GPU temperature in Celsius
    bool valid;               ///< Whether the query succeeded
};

/**
 * @brief Query GPU device information.
 *
 * Uses NVML when available (HAS_NVML), otherwise falls back to cudaMemGetInfo.
 *
 * @param[in] device_idx GPU device index (default 0)
 * @return GpuDeviceInfo with queried values
 */
GpuDeviceInfo query_gpu_info(int device_idx = 0);

/// @brief Print GPU device information to stdout
void print_gpu_info(const GpuDeviceInfo& info);

}  // namespace opt79
