#include "nvme_modes.h"

#include <cuda_runtime.h>

namespace nvme59 {
namespace {

__global__ void write_mode_count(int* device_ptr, int mode_count) {
    if (threadIdx.x == 0 && blockIdx.x == 0) {
        *device_ptr = mode_count;
    }
}

}  // namespace

void populateDeviceModeCount(int* device_ptr, int mode_count) {
    if (device_ptr == nullptr) {
        return;
    }
    write_mode_count<<<1, 1>>>(device_ptr, mode_count);
    cudaDeviceSynchronize();
}

}  // namespace nvme59
