#include "dataset_routes.h"

#include <cuda_runtime.h>

namespace dataset59 {
namespace {

__global__ void write_route_count(int* device_ptr, int route_count) {
    if (threadIdx.x == 0 && blockIdx.x == 0) {
        *device_ptr = route_count;
    }
}

}  // namespace

void populateDeviceRouteCount(int* device_ptr, int route_count) {
    if (device_ptr == nullptr) {
        return;
    }
    write_route_count<<<1, 1>>>(device_ptr, route_count);
    cudaDeviceSynchronize();
}

}  // namespace dataset59
