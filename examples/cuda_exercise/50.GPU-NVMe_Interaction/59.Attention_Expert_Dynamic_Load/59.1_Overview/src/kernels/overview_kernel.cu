#include "overview_data.h"

#include <cuda_runtime.h>

namespace overview59 {

namespace {

__global__ void write_layer_count(int* device_ptr, int layer_count) {
    if (threadIdx.x == 0 && blockIdx.x == 0) {
        *device_ptr = layer_count;
    }
}

}  // namespace

void populateDeviceLayerCount(int* device_ptr, int layer_count) {
    if (device_ptr == nullptr) {
        return;
    }
    write_layer_count<<<1, 1>>>(device_ptr, layer_count);
    cudaDeviceSynchronize();
}

}  // namespace overview59
