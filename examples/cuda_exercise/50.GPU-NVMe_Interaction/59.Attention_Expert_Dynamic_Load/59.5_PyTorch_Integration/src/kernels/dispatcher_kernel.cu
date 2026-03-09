#include "dispatcher_checks.h"

#include <cuda_runtime.h>

namespace torch59 {
namespace {

__global__ void write_check_count(int* device_ptr, int check_count) {
    if (threadIdx.x == 0 && blockIdx.x == 0) {
        *device_ptr = check_count;
    }
}

}  // namespace

void populateDeviceCheckCount(int* device_ptr, int check_count) {
    if (device_ptr == nullptr) {
        return;
    }
    write_check_count<<<1, 1>>>(device_ptr, check_count);
    cudaDeviceSynchronize();
}

}  // namespace torch59
