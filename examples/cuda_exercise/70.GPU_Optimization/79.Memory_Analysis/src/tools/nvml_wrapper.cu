/**
 * @file nvml_wrapper.cu
 * @brief Conditional NVML integration for GPU memory and utilization monitoring
 *
 * Provides a thin wrapper around NVML (NVIDIA Management Library) functions
 * to query GPU memory info, utilization, and temperature. Conditionally compiled
 * when HAS_NVML is defined.
 */
#include "tools/nvml_wrapper.h"
#include <cuda_runtime.h>
#include <cstdio>

#ifdef HAS_NVML
#include <nvml.h>
#endif

namespace opt79 {

GpuDeviceInfo query_gpu_info(int device_idx) {
    GpuDeviceInfo info = {};
    info.valid = false;

#ifdef HAS_NVML
    nvmlReturn_t result;

    result = nvmlInit_v2();
    if (result != NVML_SUCCESS) {
        fprintf(stderr, "NVML init failed: %s\n", nvmlErrorString(result));
        return info;
    }

    nvmlDevice_t device;
    result = nvmlDeviceGetHandleByIndex_v2(device_idx, &device);
    if (result != NVML_SUCCESS) {
        fprintf(stderr, "NVML get device %d failed: %s\n", device_idx, nvmlErrorString(result));
        nvmlShutdown();
        return info;
    }

    // Memory info
    nvmlMemory_t mem_info;
    result = nvmlDeviceGetMemoryInfo(device, &mem_info);
    if (result == NVML_SUCCESS) {
        info.memory_total = mem_info.total;
        info.memory_used = mem_info.used;
        info.memory_free = mem_info.free;
    }

    // Utilization
    nvmlUtilization_t util;
    result = nvmlDeviceGetUtilizationRates(device, &util);
    if (result == NVML_SUCCESS) {
        info.gpu_util = util.gpu;
        info.mem_util = util.memory;
    }

    // Temperature
    unsigned int temp;
    result = nvmlDeviceGetTemperature(device, NVML_TEMPERATURE_GPU, &temp);
    if (result == NVML_SUCCESS) {
        info.temperature = temp;
    }

    info.valid = true;
    nvmlShutdown();
#else
    // Fallback: use CUDA runtime to get memory info
    size_t free_mem, total_mem;
    cudaError_t err = cudaMemGetInfo(&free_mem, &total_mem);
    if (err == cudaSuccess) {
        info.memory_total = total_mem;
        info.memory_free = free_mem;
        info.memory_used = total_mem - free_mem;
        info.valid = true;
    }
    (void)device_idx;
#endif

    return info;
}

void print_gpu_info(const GpuDeviceInfo& info) {
    if (!info.valid) {
        printf("GPU info unavailable\n");
        return;
    }
    printf("=== GPU Device Info ===\n");
    printf("Memory total: %zu MB\n", info.memory_total / (1024 * 1024));
    printf("Memory used:  %zu MB\n", info.memory_used / (1024 * 1024));
    printf("Memory free:  %zu MB\n", info.memory_free / (1024 * 1024));
#ifdef HAS_NVML
    printf("GPU util:     %u%%\n", info.gpu_util);
    printf("Mem util:     %u%%\n", info.mem_util);
    printf("Temperature:  %u C\n", info.temperature);
#endif
    printf("=======================\n");
}

} // namespace opt79
