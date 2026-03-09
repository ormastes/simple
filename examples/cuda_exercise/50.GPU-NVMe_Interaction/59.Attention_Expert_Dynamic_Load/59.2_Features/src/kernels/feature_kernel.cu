#include "feature_matrix.h"

#include <cuda_runtime.h>

namespace features59 {

namespace {

__global__ void write_feature_count(int* device_ptr, int feature_count) {
    if (threadIdx.x == 0 && blockIdx.x == 0) {
        *device_ptr = feature_count;
    }
}

}  // namespace

void populateDeviceFeatureCount(int* device_ptr, int feature_count) {
    if (device_ptr == nullptr) {
        return;
    }
    write_feature_count<<<1, 1>>>(device_ptr, feature_count);
    cudaDeviceSynchronize();
}

}  // namespace features59
