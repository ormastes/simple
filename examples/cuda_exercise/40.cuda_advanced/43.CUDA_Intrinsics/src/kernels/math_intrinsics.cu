// math_intrinsics.cu - Fast math intrinsics demonstrations

#ifndef MATH_INTRINSICS_CU
#define MATH_INTRINSICS_CU

#include <cuda_runtime.h>

// Fast math vs standard math comparison
__global__ void fast_math_kernel(float* output, const float* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n) {
        float x = input[idx];

        // Fast intrinsics (lower precision, higher performance)
        float s = __sinf(x);
        float c = __cosf(x);
        float e = __expf(x);
        float l = __logf(x + 1.0f);

        output[idx] = s * c + e * l;
    }
}

// Standard math (higher precision, lower performance)
__global__ void standard_math_kernel(float* output, const float* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n) {
        float x = input[idx];

        // Standard math functions
        float s = sinf(x);
        float c = cosf(x);
        float e = expf(x);
        float l = logf(x + 1.0f);

        output[idx] = s * c + e * l;
    }
}

// Fast square root and reciprocal operations
__global__ void fast_sqrt_rsqrt_kernel(float* output, const float* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n) {
        float x = input[idx];

        // Fast square root
        float sqrt_val = __fsqrt_rn(x);  // Round to nearest

        // Fast reciprocal square root (1/sqrt(x))
        float rsqrt_val = __frsqrt_rn(x);

        // Fast division using reciprocal
        float rcp_val = __frcp_rn(x);

        output[idx] = sqrt_val + rsqrt_val + rcp_val;
    }
}

// Integer intrinsics: population count, find first set bit, etc.
__global__ void integer_intrinsics_kernel(unsigned int* output, const unsigned int* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n) {
        unsigned int val = input[idx];

        // Population count (count number of 1 bits)
        unsigned int popcount = __popc(val);

        // Find first set bit (counting from LSB)
        unsigned int ffs = __ffs(val);

        // Count leading zeros
        unsigned int clz = __clz(val);

        // Byte-level permutation
        unsigned int byte_perm = __byte_perm(val, val >> 8, 0x0123);

        output[idx] = popcount + ffs + clz + byte_perm;
    }
}

// Fused multiply-add operations
__global__ void fma_kernel(float* output, const float* a, const float* b, const float* c, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n) {
        // Fused multiply-add: a * b + c (single rounding)
        output[idx] = __fmaf_rn(a[idx], b[idx], c[idx]);
    }
}

// Double precision fast math (on supported architectures)
__global__ void double_fast_math_kernel(double* output, const double* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n) {
        double x = input[idx];

        // Double precision fast math
        double s = sin(x);  // No __sin for double
        double c = cos(x);
        double sqrt_val = sqrt(x);

        // Fused multiply-add for double
        output[idx] = fma(s, c, sqrt_val);
    }
}

// Half precision operations (FP16)
__global__ void half_precision_kernel(half* output, const half* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n) {
        half x = input[idx];

        // Half precision arithmetic
        half y = __hadd(x, x);           // x + x
        half z = __hmul(y, __float2half(2.0f));  // 2 * (x + x)

        output[idx] = z;
    }
}

// Saturation arithmetic (clamp to [0, 1])
__global__ void saturate_kernel(float* output, const float* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n) {
        float x = input[idx];

        // Saturate to [0, 1] range
        output[idx] = __saturatef(x);
    }
}

// Min/Max intrinsics
__global__ void minmax_kernel(float* output_min, float* output_max,
                               const float* a, const float* b, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < n) {
        // Fast min/max operations
        output_min[idx] = fminf(a[idx], b[idx]);
        output_max[idx] = fmaxf(a[idx], b[idx]);
    }
}

#endif // MATH_INTRINSICS_CU
