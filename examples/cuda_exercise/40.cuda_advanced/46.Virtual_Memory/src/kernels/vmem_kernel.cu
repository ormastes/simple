// vmem_kernel.cu - Kernels for demonstrating virtual memory concepts

#include <cuda_runtime.h>

// Simple kernel to initialize memory with a pattern
__global__ void init_vmem_pattern(int* data, int n, int offset) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        data[idx] = idx + offset;
    }
}

// Kernel to verify memory contents
__global__ void verify_vmem_pattern(const int* data, int n, int offset, bool* result) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        if (data[idx] != idx + offset) {
            *result = false;
        }
    }
}

// Kernel to demonstrate memory access patterns with virtual memory
__global__ void vmem_stride_access(int* output, const int* input, int n, int stride) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        int src_idx = (idx * stride) % n;
        output[idx] = input[src_idx];
    }
}

// Kernel to demonstrate shared memory with virtual memory
__global__ void vmem_shared_reduce(int* output, const int* input, int n) {
    __shared__ int sdata[256];

    int tid = threadIdx.x;
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Load data into shared memory
    sdata[tid] = (idx < n) ? input[idx] : 0;
    __syncthreads();

    // Reduce in shared memory
    for (int s = blockDim.x / 2; s > 0; s >>= 1) {
        if (tid < s) {
            sdata[tid] += sdata[tid + s];
        }
        __syncthreads();
    }

    // Write result
    if (tid == 0) {
        output[blockIdx.x] = sdata[0];
    }
}

// Kernel to demonstrate coalesced access with virtual memory
__global__ void vmem_coalesced_copy(int* output, const int* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Coalesced access: adjacent threads access adjacent memory locations
    if (idx < n) {
        output[idx] = input[idx];
    }
}

// Kernel to demonstrate uncoalesced access (for comparison)
__global__ void vmem_uncoalesced_copy(int* output, const int* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Uncoalesced access: reversed order
    if (idx < n) {
        int reverse_idx = n - 1 - idx;
        output[idx] = input[reverse_idx];
    }
}
