/**
 * Parallel Reduction with Shared Memory (Part 23)
 *
 * Demonstrates evolution of reduction algorithms from naive to highly optimized
 * Shows impact of different memory access patterns and bank conflicts
 *
 * Key concepts:
 * - Shared memory for inter-thread communication
 * - Bank conflict avoidance patterns
 * - Sequential addressing vs. interleaved addressing
 * - Warp divergence minimization
 */

#include <iostream>
#include <cuda_runtime.h>
#include "cuda_utils.h"  // From CudaCustomLib

#define BLOCK_SIZE 256

// =============================================================================
// Reduction 1: Interleaved Addressing (Divergent, Bank Conflicts)
// =============================================================================

/**
 * Interleaved addressing reduction (poorest performance)
 *
 * Issues:
 * - Warp divergence: Half of threads idle after each iteration
 * - Bank conflicts: Stride increases each iteration (1, 2, 4, 8, ...)
 * - Effective bandwidth: ~80 GB/s
 */
__global__ void reduce_interleaved(float* g_out, const float* g_in, int N) {
    extern __shared__ float sdata[];

    int tid = threadIdx.x;
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Load data into shared memory
    sdata[tid] = (idx < N) ? g_in[idx] : 0.0f;
    __syncthreads();

    // Interleaved reduction with bank conflicts
    for (int stride = 1; stride < blockDim.x; stride *= 2) {
        if (tid % (2 * stride) == 0) {  // Warp divergence!
            sdata[tid] += sdata[tid + stride];
        }
        __syncthreads();
    }

    if (tid == 0) {
        g_out[blockIdx.x] = sdata[0];
    }
}

// =============================================================================
// Reduction 2: Sequential Addressing (No Divergence, No Bank Conflicts)
// =============================================================================

/**
 * Sequential addressing reduction (much better)
 *
 * Improvements:
 * - No warp divergence: Active threads are contiguous
 * - No bank conflicts: Sequential access pattern
 * - Effective bandwidth: ~300 GB/s
 *
 * Shared memory access pattern:
 *   Iteration 1: stride = blockDim.x / 2 = 128
 *     Threads 0-127 access sdata[0-127] and sdata[128-255]
 *     No bank conflicts (different banks)
 *   Iteration 2: stride = 64
 *     Threads 0-63 access sdata[0-63] and sdata[64-127]
 *   ...
 */
__global__ void reduce_sequential(float* g_out, const float* g_in, int N) {
    extern __shared__ float sdata[];

    int tid = threadIdx.x;
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Load data into shared memory
    sdata[tid] = (idx < N) ? g_in[idx] : 0.0f;
    __syncthreads();

    // Sequential addressing reduction
    for (int stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (tid < stride) {
            sdata[tid] += sdata[tid + stride];
        }
        __syncthreads();
    }

    if (tid == 0) {
        g_out[blockIdx.x] = sdata[0];
    }
}

// =============================================================================
// Reduction 3: First Add During Load (Reduced Work)
// =============================================================================

/**
 * Reduction with first add during global load
 *
 * Optimization:
 * - Each thread loads 2 elements and adds them during load
 * - Halves the number of blocks needed
 * - Reduces global memory accesses
 * - Effective bandwidth: ~450 GB/s
 */
__global__ void reduce_first_add(float* g_out, const float* g_in, int N) {
    extern __shared__ float sdata[];

    int tid = threadIdx.x;
    int idx = blockIdx.x * (blockDim.x * 2) + threadIdx.x;

    // Load and add two elements from global memory
    float sum = 0.0f;
    if (idx < N) sum += g_in[idx];
    if (idx + blockDim.x < N) sum += g_in[idx + blockDim.x];
    sdata[tid] = sum;
    __syncthreads();

    // Sequential addressing reduction
    for (int stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (tid < stride) {
            sdata[tid] += sdata[tid + stride];
        }
        __syncthreads();
    }

    if (tid == 0) {
        g_out[blockIdx.x] = sdata[0];
    }
}

// =============================================================================
// Reduction 4: Unroll Last Warp (No Synchronization)
// =============================================================================

/**
 * Warp-level reduction without synchronization
 *
 * Optimization:
 * - Last 32 elements (one warp) don't need __syncthreads()
 * - Threads in a warp execute in lockstep (SIMT)
 * - Saves synchronization overhead
 * - Effective bandwidth: ~550 GB/s
 */
__device__ void warp_reduce(volatile float* sdata, int tid) {
    // No __syncthreads() needed within a warp!
    sdata[tid] += sdata[tid + 32];
    sdata[tid] += sdata[tid + 16];
    sdata[tid] += sdata[tid + 8];
    sdata[tid] += sdata[tid + 4];
    sdata[tid] += sdata[tid + 2];
    sdata[tid] += sdata[tid + 1];
}

__global__ void reduce_unroll_warp(float* g_out, const float* g_in, int N) {
    extern __shared__ float sdata[];

    int tid = threadIdx.x;
    int idx = blockIdx.x * (blockDim.x * 2) + threadIdx.x;

    // Load and add two elements
    float sum = 0.0f;
    if (idx < N) sum += g_in[idx];
    if (idx + blockDim.x < N) sum += g_in[idx + blockDim.x];
    sdata[tid] = sum;
    __syncthreads();

    // Sequential reduction until we reach one warp
    for (int stride = blockDim.x / 2; stride > 32; stride >>= 1) {
        if (tid < stride) {
            sdata[tid] += sdata[tid + stride];
        }
        __syncthreads();
    }

    // Warp-level reduction (no sync needed)
    if (tid < 32) {
        warp_reduce(sdata, tid);
    }

    if (tid == 0) {
        g_out[blockIdx.x] = sdata[0];
    }
}

// =============================================================================
// Reduction 5: Completely Unrolled (Maximum Performance)
// =============================================================================

/**
 * Fully unrolled reduction (best performance)
 *
 * Optimization:
 * - All loops unrolled at compile time
 * - Compiler can optimize register usage
 * - No loop overhead
 * - Template for different block sizes
 * - Effective bandwidth: ~700 GB/s (near peak!)
 */
template<unsigned int BLOCK_SIZE_TEMPLATE>
__device__ void warp_reduce_template(volatile float* sdata, int tid) {
    if (BLOCK_SIZE_TEMPLATE >= 64) sdata[tid] += sdata[tid + 32];
    if (BLOCK_SIZE_TEMPLATE >= 32) sdata[tid] += sdata[tid + 16];
    if (BLOCK_SIZE_TEMPLATE >= 16) sdata[tid] += sdata[tid + 8];
    if (BLOCK_SIZE_TEMPLATE >= 8) sdata[tid] += sdata[tid + 4];
    if (BLOCK_SIZE_TEMPLATE >= 4) sdata[tid] += sdata[tid + 2];
    if (BLOCK_SIZE_TEMPLATE >= 2) sdata[tid] += sdata[tid + 1];
}

template<unsigned int BLOCK_SIZE_TEMPLATE>
__global__ void reduce_unrolled(float* g_out, const float* g_in, int N) {
    extern __shared__ float sdata[];

    int tid = threadIdx.x;
    int idx = blockIdx.x * (BLOCK_SIZE_TEMPLATE * 2) + threadIdx.x;

    // Load and add
    float sum = 0.0f;
    if (idx < N) sum += g_in[idx];
    if (idx + BLOCK_SIZE_TEMPLATE < N) sum += g_in[idx + BLOCK_SIZE_TEMPLATE];
    sdata[tid] = sum;
    __syncthreads();

    // Completely unrolled reduction
    if (BLOCK_SIZE_TEMPLATE >= 512) { if (tid < 256) sdata[tid] += sdata[tid + 256]; __syncthreads(); }
    if (BLOCK_SIZE_TEMPLATE >= 256) { if (tid < 128) sdata[tid] += sdata[tid + 128]; __syncthreads(); }
    if (BLOCK_SIZE_TEMPLATE >= 128) { if (tid < 64) sdata[tid] += sdata[tid + 64]; __syncthreads(); }

    if (tid < 32) {
        warp_reduce_template<BLOCK_SIZE_TEMPLATE>(sdata, tid);
    }

    if (tid == 0) {
        g_out[blockIdx.x] = sdata[0];
    }
}

// =============================================================================
// Host Code
// =============================================================================

float cpu_reduce(const float* data, int N) {
    float sum = 0.0f;
    for (int i = 0; i < N; i++) {
        sum += data[i];
    }
    return sum;
}

int main() {
    const int N = 32 * 1024 * 1024;  // 32M elements
    size_t bytes = N * sizeof(float);

    printf("Array size: %d elements (%.2f MB)\n", N, bytes / 1024.0f / 1024.0f);

    // Allocate and initialize host data
    float *h_input = new float[N];
    for (int i = 0; i < N; i++) {
        h_input[i] = 1.0f;  // Sum should be N
    }

    float expected = cpu_reduce(h_input, N);
    printf("Expected sum: %.2f\n\n", expected);

    // Allocate device memory
    float *d_input, *d_partial;
    int num_blocks = (N + BLOCK_SIZE * 2 - 1) / (BLOCK_SIZE * 2);
    CHECK_CUDA(cudaMalloc(&d_input, bytes));
    CHECK_CUDA(cudaMalloc(&d_partial, num_blocks * sizeof(float)));
    CHECK_CUDA(cudaMemcpy(d_input, h_input, bytes, cudaMemcpyHostToDevice));

    int shared_mem_size = BLOCK_SIZE * sizeof(float);

    // =============================================================================
    // Test Each Reduction Variant
    // =============================================================================

    auto test_reduction = [&](const char* name, auto kernel_func, int blocks_multiplier = 1) {
        int blocks = (N + BLOCK_SIZE * blocks_multiplier - 1) / (BLOCK_SIZE * blocks_multiplier);

        cudaEvent_t start, stop;
        CHECK_CUDA(cudaEventCreate(&start));
        CHECK_CUDA(cudaEventCreate(&stop));

        // Warm-up
        kernel_func<<<blocks, BLOCK_SIZE, shared_mem_size>>>(d_partial, d_input, N);
        CHECK_CUDA(cudaDeviceSynchronize());

        // Benchmark
        CHECK_CUDA(cudaEventRecord(start));
        for (int i = 0; i < 100; i++) {
            kernel_func<<<blocks, BLOCK_SIZE, shared_mem_size>>>(d_partial, d_input, N);
        }
        CHECK_CUDA(cudaEventRecord(stop));
        CHECK_CUDA(cudaEventSynchronize(stop));

        float ms = 0;
        CHECK_CUDA(cudaEventElapsedTime(&ms, start, stop));
        ms /= 100.0f;  // Average

        // Copy partial results and finish on CPU
        float *h_partial = new float[blocks];
        CHECK_CUDA(cudaMemcpy(h_partial, d_partial, blocks * sizeof(float), cudaMemcpyDeviceToHost));

        float result = 0.0f;
        for (int i = 0; i < blocks; i++) {
            result += h_partial[i];
        }

        float bandwidth_gb = bytes / (ms / 1000.0f) / 1e9f;
        float error = fabsf(result - expected) / expected * 100.0f;

        printf("[%s]\n", name);
        printf("  Time: %.3f ms\n", ms);
        printf("  Bandwidth: %.2f GB/s\n", bandwidth_gb);
        printf("  Result: %.2f (error: %.6f%%)\n", result, error);
        printf("  %s\n\n", error < 0.01f ? "✓ PASS" : "✗ FAIL");

        delete[] h_partial;
        CHECK_CUDA(cudaEventDestroy(start));
        CHECK_CUDA(cudaEventDestroy(stop));
    };

    test_reduction("Interleaved (Divergent)", reduce_interleaved);
    test_reduction("Sequential (No Divergence)", reduce_sequential);
    test_reduction("First Add During Load", reduce_first_add, 2);
    test_reduction("Unroll Last Warp", reduce_unroll_warp, 2);
    test_reduction("Completely Unrolled", reduce_unrolled<BLOCK_SIZE>, 2);

    // Cleanup
    delete[] h_input;
    CHECK_CUDA(cudaFree(d_input));
    CHECK_CUDA(cudaFree(d_partial));

    printf("✓ Parallel reduction demonstration complete!\n");
    return 0;
}
