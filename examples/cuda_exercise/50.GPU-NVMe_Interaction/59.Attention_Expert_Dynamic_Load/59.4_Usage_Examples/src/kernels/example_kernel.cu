#include "example_registry.h"

#include <cuda_runtime.h>

namespace examples59 {
namespace {

__global__ void write_snippet_count(int* device_ptr, int snippet_count) {
    if (threadIdx.x == 0 && blockIdx.x == 0) {
        *device_ptr = snippet_count;
    }
}

}  // namespace

void populateDeviceSnippetCount(int* device_ptr, int snippet_count) {
    if (device_ptr == nullptr) {
        return;
    }
    write_snippet_count<<<1, 1>>>(device_ptr, snippet_count);
    cudaDeviceSynchronize();
}

}  // namespace examples59
