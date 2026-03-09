// vector_add_2d.cu - 2D vector operations implementation
#include "vector_add_2d.h"
#include <cstdio>
#include <cassert>
#include <cmath>

// Simple 2D vector addition kernel - computes square(A) + B
__global__ void vector_add_2d(const float* A, const float* B, float* C, int width, int height) {
    int x = blockIdx.x * blockDim.x + threadIdx.x;
    int y = blockIdx.y * blockDim.y + threadIdx.y;
    int i = y * width + x;  // Row-major access

    if (x < width && y < height) {
        C[i] = A[i] * A[i] + B[i];  // Compute square(A) + B
    }
}

// Reduction sum kernel (sum all elements)
__global__ void reduce_sum(const float* input, float* output, int N, int stride) {
    extern __shared__ float sdata[];

    unsigned int tid = threadIdx.x;
    unsigned int i = blockIdx.x * blockDim.x * 2 + threadIdx.x;  // Grid-stride loop

    // Coalesced load with grid-stride loop to handle strided patterns better
    float sum = 0.0f;

    // First, accumulate multiple elements per thread (coalesced reads)
    while (i < N) {
        sum += input[i];
        if (i + blockDim.x < N)
            sum += input[i + blockDim.x];  // Load two elements per thread
        i += gridDim.x * blockDim.x * 2;  // Grid-stride loop
    }

    // Store in shared memory
    sdata[tid] = sum;
    __syncthreads();

    // Reduction in shared memory (unrolled for better performance)
    if (blockDim.x >= 512) {
        if (tid < 256) { sdata[tid] += sdata[tid + 256]; } __syncthreads();
    }
    if (blockDim.x >= 256) {
        if (tid < 128) { sdata[tid] += sdata[tid + 128]; } __syncthreads();
    }
    if (blockDim.x >= 128) {
        if (tid < 64) { sdata[tid] += sdata[tid + 64]; } __syncthreads();
    }

    // Warp-level reduction using shuffle (modern CUDA 13+ approach)
    if (tid < 32) {
        // Use warp shuffle instead of volatile (avoids deprecated warning)
        float val = sdata[tid];
        if (blockDim.x >= 64) val += sdata[tid + 32];
        __syncwarp();  // Ensure all warps have loaded from shared memory

        // Warp shuffle reduction (no __syncwarp needed within shuffle operations)
        for (int offset = 16; offset > 0; offset /= 2) {
            val += __shfl_down_sync(0xffffffff, val, offset);
        }

        if (tid == 0) sdata[0] = val;
    }

    // Write result for this block to global memory
    if (tid == 0) {
        atomicAdd(output, sdata[0]);
    }
}

// Kernel with intentional bug (missing boundary check)
__global__ void vector_add_2d_with_bug(const float* a, const float* b, float* c, int width, int height) {
    int x = blockIdx.x * blockDim.x + threadIdx.x;
    int y = blockIdx.y * blockDim.y + threadIdx.y;

    // BUG: Missing boundary check - will cause out-of-bounds access
    int idx = y * width + x;
    c[idx] = a[idx] + b[idx];
}

// Kernel with assertion for debugging
__global__ void vector_add_2d_with_assert(const float* a, const float* b, float* c, int width, int height) {
    int x = blockIdx.x * blockDim.x + threadIdx.x;
    int y = blockIdx.y * blockDim.y + threadIdx.y;

    if (x < width && y < height) {
        int idx = y * width + x;
        // Assert that input values are valid (not NaN)
        assert(!isnan(a[idx]) && !isnan(b[idx]));
        c[idx] = a[idx] + b[idx];
        // Assert that output is valid
        assert(!isnan(c[idx]));
    }
}