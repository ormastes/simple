// scheduling_kernels.cu - Kernels for demonstrating hardware scheduling concepts

#include <cuda_runtime.h>

// Simple kernel with minimal resource usage - high occupancy
__global__ void low_resource_kernel(float* output, const float* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        output[idx] = input[idx] * 2.0f;
    }
}

// Kernel with heavy register usage - lower occupancy
__global__ void high_register_kernel(float* output, const float* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        // Use many registers to demonstrate register pressure
        float r0 = input[idx];
        float r1 = r0 * 1.1f;
        float r2 = r1 * 1.2f;
        float r3 = r2 * 1.3f;
        float r4 = r3 * 1.4f;
        float r5 = r4 * 1.5f;
        float r6 = r5 * 1.6f;
        float r7 = r6 * 1.7f;
        float r8 = r7 * 1.8f;
        float r9 = r8 * 1.9f;

        output[idx] = r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9;
    }
}

// Kernel with heavy shared memory usage
template<int SHARED_SIZE>
__global__ void high_shared_mem_kernel(float* output, const float* input, int n) {
    __shared__ float smem[SHARED_SIZE];

    int tid = threadIdx.x;
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Load data into shared memory
    if (tid < SHARED_SIZE && idx < n) {
        smem[tid] = input[idx];
    }
    __syncthreads();

    // Process data from shared memory
    if (idx < n) {
        float sum = 0.0f;
        for (int i = 0; i < SHARED_SIZE && i < blockDim.x; i++) {
            sum += smem[i];
        }
        output[idx] = sum / SHARED_SIZE;
    }
}

// Kernel for measuring basic scheduling behavior
__global__ void measure_scheduling_kernel(float* output, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        output[idx] = sqrtf(static_cast<float>(idx));
    }
}

// Grid-stride loop kernel - optimal for varying problem sizes
__global__ void grid_stride_kernel(float* output, const float* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    int stride = blockDim.x * gridDim.x;

    for (int i = idx; i < n; i += stride) {
        output[i] = sqrtf(input[i]) + sinf(input[i]);
    }
}

// Warp-level scheduling demonstration
__global__ void warp_scheduling_kernel(int* output, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    int warpId = threadIdx.x / 32;
    int laneId = threadIdx.x % 32;

    if (idx < n) {
        int value = warpId * 1000 + laneId;

        // Warp-level operations
        value += __shfl_xor_sync(0xffffffff, value, 1);
        value += __shfl_xor_sync(0xffffffff, value, 2);

        output[idx] = value;
    }
}

// Explicit template instantiations
template __global__ void high_shared_mem_kernel<512>(float*, const float*, int);
template __global__ void high_shared_mem_kernel<1024>(float*, const float*, int);
template __global__ void high_shared_mem_kernel<2048>(float*, const float*, int);
