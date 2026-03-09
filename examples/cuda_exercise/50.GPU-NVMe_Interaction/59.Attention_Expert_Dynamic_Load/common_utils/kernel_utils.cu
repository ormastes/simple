/**
 * @file kernel_utils.cu
 * @brief Shared CUDA kernel utilities for Module 59
 *
 * Eliminates duplicate kernel code across all 9 submodules
 */

#include "kernel_utils.h"
#include <cuda_runtime.h>

namespace module59 {
namespace kernel {

namespace {

/**
 * @brief Generic kernel to write a single integer value to device memory
 *
 * This kernel was duplicated 9 times across all submodules
 */
__global__ void write_single_value(int* device_ptr, int value) {
    if (threadIdx.x == 0 && blockIdx.x == 0) {
        *device_ptr = value;
    }
}

} // anonymous namespace

void writeIntegerToDevice(int* device_ptr, int value) {
    if (device_ptr == nullptr) {
        return;
    }
    write_single_value<<<1, 1>>>(device_ptr, value);
    cudaDeviceSynchronize();
}

} // namespace kernel
} // namespace module59