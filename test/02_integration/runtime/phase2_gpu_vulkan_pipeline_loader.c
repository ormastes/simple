#ifdef PHASE2_GPU_PIPELINE_BASELINE
#define SIMPLE_GPU_VULKAN_PIPELINE_PRIVATE_H
#endif
#include PHASE2_GPU_PIPELINE_LOADER_SOURCE
#ifndef PHASE2_GPU_PIPELINE_BASELINE
#include "runtime_gpu_vulkan_pipeline_private.h"
#endif
int64_t phase2_gpu_vulkan_pipeline_provider_counter(int64_t which) {
    const char *names[] = {"phase2_gpu_vulkan_pipeline_failures",
        "phase2_gpu_vulkan_pipeline_calls", "phase2_gpu_vulkan_pipeline_glsl_diagnostic"};
    SimpleGpuCallPinV1 pin;
    int64_t result;
    if (which < 0 || which > 2 || !simple_gpu_call_acquire_v1(
            SIMPLE_GPU_BACKEND_VULKAN, names[which], &pin)) return -1;
    result = ((int64_t (*)(void))pin.symbol)();
    simple_gpu_call_release_v1(&pin);
    return result;
}
