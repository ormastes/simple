#include "build_recipe.h"

#include <cuda_runtime.h>

namespace build59 {
namespace {

__global__ void write_step_count(int* device_ptr, int step_count) {
    if (threadIdx.x == 0 && blockIdx.x == 0) {
        *device_ptr = step_count;
    }
}

}  // namespace

void populateDeviceStepCount(int* device_ptr, int step_count) {
    if (device_ptr == nullptr) {
        return;
    }
    write_step_count<<<1, 1>>>(device_ptr, step_count);
    cudaDeviceSynchronize();
}

}  // namespace build59
