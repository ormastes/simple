// ipc_kernel.cu - Simple kernels for IPC demonstration

#ifndef IPC_KERNEL_CU
#define IPC_KERNEL_CU

#include <cuda_runtime.h>

// Simple initialization kernel for IPC memory
__global__ void initialize_ipc_data(float* data, float value, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        data[idx] = value;
    }
}

// Simple increment kernel for IPC memory
__global__ void increment_ipc_data(float* data, float delta, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        data[idx] += delta;
    }
}

// Simple verification kernel
__global__ void verify_ipc_data(const float* data, float expected, bool* result, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        if (fabsf(data[idx] - expected) > 1e-5f) {
            *result = false;
        }
    }
}

#endif // IPC_KERNEL_CU
