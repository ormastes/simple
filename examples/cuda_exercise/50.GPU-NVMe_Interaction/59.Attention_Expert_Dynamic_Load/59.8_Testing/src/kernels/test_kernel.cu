#include "test_matrix.h"

#include <cuda_runtime.h>

namespace testing59 {
namespace {

__global__ void write_test_count(int* device_ptr, int test_count) {
    if (threadIdx.x == 0 && blockIdx.x == 0) {
        *device_ptr = test_count;
    }
}

}  // namespace

void populateDeviceTestCount(int* device_ptr, int test_count) {
    if (device_ptr == nullptr) {
        return;
    }
    write_test_count<<<1, 1>>>(device_ptr, test_count);
    cudaDeviceSynchronize();
}

}  // namespace testing59
