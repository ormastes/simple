// register_optimization.cu - Register pressure management demonstrations

#ifndef REGISTER_OPTIMIZATION_CU
#define REGISTER_OPTIMIZATION_CU

#include <cuda_runtime.h>

// High register pressure - uses many registers
__global__ void high_register_kernel(float* output, const float* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= n) return;

    // Many local variables = high register usage
    float a1 = input[idx];
    float a2 = a1 * 2.0f;
    float a3 = a2 + 1.0f;
    float a4 = sinf(a3);
    float a5 = cosf(a3);
    float a6 = a4 * a5;
    float a7 = a6 + a1;
    float a8 = sqrtf(fabsf(a7));

    output[idx] = a8;
}

// Low register pressure - reuses variables
__global__ void __launch_bounds__(256, 4)
low_register_kernel(float* output, const float* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= n) return;

    // Reuse variables to reduce register count
    float val = input[idx];
    float orig = val;
    val = val * 2.0f + 1.0f;
    float temp = sinf(val);
    val = temp * cosf(val) + orig;
    output[idx] = sqrtf(fabsf(val));
}

// Optimized with launch bounds for occupancy
__global__ void __launch_bounds__(256, 2)
occupancy_optimized_kernel(float* data, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        data[idx] = data[idx] * 2.0f + 1.0f;
    }
}

// No launch bounds - compiler prioritizes performance
__global__ void performance_first_kernel(float* data, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        float val = data[idx];
        val = val * val * val * val;
        data[idx] = val;
    }
}

#endif // REGISTER_OPTIMIZATION_CU
