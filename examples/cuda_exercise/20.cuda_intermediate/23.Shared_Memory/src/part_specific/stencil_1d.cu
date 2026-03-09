/**
 * 1D Stencil Computation with Shared Memory (Part 23)
 *
 * Demonstrates efficient stencil operations using shared memory
 * with halo cells for boundary handling
 *
 * Key concepts:
 * - Shared memory for neighbor access
 * - Halo cell loading strategies
 * - Memory access coalescing
 * - Boundary condition handling
 */

#include <iostream>
#include <cuda_runtime.h>
#include "cuda_utils.h"  // From CudaCustomLib

#define RADIUS 3
#define BLOCK_SIZE 256

// =============================================================================
// Naive 1D Stencil (Global Memory Only)
// =============================================================================

/**
 * Naive 1D stencil reading directly from global memory
 *
 * Stencil pattern: 7-point (radius 3)
 *   output[i] = c0 * input[i] +
 *               c1 * (input[i-1] + input[i+1]) +
 *               c2 * (input[i-2] + input[i+2]) +
 *               c3 * (input[i-3] + input[i+3])
 *
 * Performance issues:
 * - Each thread reads 7 elements from global memory
 * - Overlapping reads between threads (neighbors share data)
 * - For 256-thread block: ~1,792 global reads (256 * 7)
 * - But only ~262 unique elements needed (256 + 2*3)
 * - Bandwidth waste: ~6-7x redundant reads!
 * - Effective bandwidth: ~120 GB/s
 */
__global__ void stencil_1d_naive(float* output, const float* input, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx >= RADIUS && idx < N - RADIUS) {
        // Apply 7-point stencil
        float result = 1.0f * input[idx];
        result += 0.5f * (input[idx - 1] + input[idx + 1]);
        result += 0.25f * (input[idx - 2] + input[idx + 2]);
        result += 0.125f * (input[idx - 3] + input[idx + 3]);

        output[idx] = result / 3.75f;  // Normalize
    } else if (idx < N) {
        // Boundary: copy input
        output[idx] = input[idx];
    }
}

// =============================================================================
// Optimized 1D Stencil (Shared Memory with Halo Cells)
// =============================================================================

/**
 * Optimized 1D stencil using shared memory caching
 *
 * Shared memory usage:
 *   temp[BLOCK_SIZE + 2 * RADIUS]: Block tile + halo cells
 *   For BLOCK_SIZE=256, RADIUS=3: 262 floats = 1,048 bytes (~1 KB)
 *
 * Halo cells visualization (RADIUS=3):
 * ┌────────────────────────────────────────────────────────┐
 * │ Left Halo │    Main Block (256 threads)    │ Right Halo│
 * │  [0..2]   │         [3..258]               │ [259..261]│
 * │ ←-3 elem  │         256 elem               │  3 elem-→ │
 * └────────────────────────────────────────────────────────┘
 *
 * Loading strategy:
 * 1. Each thread loads its corresponding element
 * 2. First RADIUS threads load left halo
 * 3. First RADIUS threads load right halo
 * 4. Total global reads: 262 per block (vs 1,792 in naive)
 *
 * Performance:
 * - Global reads reduced by ~6-7x
 * - All stencil accesses use fast shared memory
 * - Effective bandwidth: ~750 GB/s
 * - Speedup: ~6x vs naive
 */
__global__ void stencil_1d_shared(float* output, const float* input, int N) {
    // Shared memory: block data + halo cells on both sides
    __shared__ float temp[BLOCK_SIZE + 2 * RADIUS];

    int global_idx = blockIdx.x * blockDim.x + threadIdx.x;
    int local_idx = threadIdx.x + RADIUS;  // Offset for halo

    // Load main block element into shared memory
    if (global_idx < N) {
        temp[local_idx] = input[global_idx];
    } else {
        temp[local_idx] = 0.0f;
    }

    // Load left halo cells (first RADIUS threads)
    if (threadIdx.x < RADIUS) {
        int halo_idx = global_idx - RADIUS;
        temp[threadIdx.x] = (halo_idx >= 0) ? input[halo_idx] : 0.0f;
    }

    // Load right halo cells (first RADIUS threads)
    if (threadIdx.x < RADIUS) {
        int halo_idx = global_idx + BLOCK_SIZE;
        temp[local_idx + BLOCK_SIZE] = (halo_idx < N) ? input[halo_idx] : 0.0f;
    }

    __syncthreads();

    // Apply stencil using cached shared memory data
    if (global_idx >= RADIUS && global_idx < N - RADIUS) {
        // All accesses to temp[] hit shared memory (fast!)
        float result = 1.0f * temp[local_idx];
        result += 0.5f * (temp[local_idx - 1] + temp[local_idx + 1]);
        result += 0.25f * (temp[local_idx - 2] + temp[local_idx + 2]);
        result += 0.125f * (temp[local_idx - 3] + temp[local_idx + 3]);

        output[global_idx] = result / 3.75f;
    } else if (global_idx < N) {
        // Boundary: copy input
        output[global_idx] = input[global_idx];
    }
}

// =============================================================================
// Alternative: Read-Only Cache Optimization
// =============================================================================

/**
 * Stencil using __ldg() for read-only cache optimization
 *
 * __ldg() benefits:
 * - Routes loads through read-only/texture cache instead of L1
 * - Read-only cache: 48 KB, higher bandwidth for read-only data
 * - Automatic caching of neighboring elements
 * - Good alternative when shared memory is limited
 *
 * Performance:
 * - Effective bandwidth: ~600 GB/s
 * - Faster than naive, but slower than explicit shared memory
 * - Less programmer control than shared memory
 * - Best for simple stencils or when shared memory is constrained
 */
__global__ void stencil_1d_ldg(float* output, const float* input, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx >= RADIUS && idx < N - RADIUS) {
        // Use __ldg() for read-only cache optimization
        float result = 1.0f * __ldg(&input[idx]);
        result += 0.5f * (__ldg(&input[idx - 1]) + __ldg(&input[idx + 1]));
        result += 0.25f * (__ldg(&input[idx - 2]) + __ldg(&input[idx + 2]));
        result += 0.125f * (__ldg(&input[idx - 3]) + __ldg(&input[idx + 3]));

        output[idx] = result / 3.75f;
    } else if (idx < N) {
        output[idx] = input[idx];
    }
}

// =============================================================================
// Host Code
// =============================================================================

void verify_stencil(const float* h_out_ref, const float* h_out, int N) {
    bool correct = true;
    int errors = 0;
    const int MAX_ERRORS = 10;

    for (int i = 0; i < N && errors < MAX_ERRORS; i++) {
        if (fabsf(h_out_ref[i] - h_out[i]) > 1e-5f) {
            if (errors < MAX_ERRORS) {
                printf("Mismatch at [%d]: expected %.6f, got %.6f\n",
                       i, h_out_ref[i], h_out[i]);
            }
            correct = false;
            errors++;
        }
    }

    if (correct) {
        printf("✓ Stencil correct!\n");
    } else {
        printf("✗ Stencil incorrect (%d errors shown)\n", std::min(errors, MAX_ERRORS));
    }
}

int main() {
    const int N = 32 * 1024 * 1024;  // 32M elements
    size_t bytes = N * sizeof(float);

    printf("Array size: %d elements (%.2f MB)\n", N, bytes / 1024.0f / 1024.0f);
    printf("Stencil radius: %d (7-point stencil)\n\n", RADIUS);

    // Allocate host memory
    float *h_input = new float[N];
    float *h_output_ref = new float[N];
    float *h_output = new float[N];

    // Initialize input with sine wave
    for (int i = 0; i < N; i++) {
        h_input[i] = sinf(i * 0.001f);
    }

    // Allocate device memory
    float *d_input, *d_output;
    CHECK_CUDA(cudaMalloc(&d_input, bytes));
    CHECK_CUDA(cudaMalloc(&d_output, bytes));
    CHECK_CUDA(cudaMemcpy(d_input, h_input, bytes, cudaMemcpyHostToDevice));

    dim3 block(BLOCK_SIZE);
    dim3 grid((N + BLOCK_SIZE - 1) / BLOCK_SIZE);

    // Warm-up
    stencil_1d_shared<<<grid, block>>>(d_output, d_input, N);
    CHECK_CUDA(cudaDeviceSynchronize());

    // =============================================================================
    // Benchmark 1: Naive Stencil
    // =============================================================================
    {
        cudaEvent_t start, stop;
        CHECK_CUDA(cudaEventCreate(&start));
        CHECK_CUDA(cudaEventCreate(&stop));

        CHECK_CUDA(cudaEventRecord(start));
        stencil_1d_naive<<<grid, block>>>(d_output, d_input, N);
        CHECK_CUDA(cudaEventRecord(stop));
        CHECK_CUDA(cudaEventSynchronize(stop));

        float ms = 0;
        CHECK_CUDA(cudaEventElapsedTime(&ms, start, stop));

        // Bandwidth: read 7 values + write 1 per element
        float bandwidth_gb = (8.0f * bytes) / (ms / 1000.0f) / 1e9f;
        printf("[Naive Stencil]\n");
        printf("  Time: %.3f ms\n", ms);
        printf("  Bandwidth: %.2f GB/s\n", bandwidth_gb);

        CHECK_CUDA(cudaMemcpy(h_output_ref, d_output, bytes, cudaMemcpyDeviceToHost));

        CHECK_CUDA(cudaEventDestroy(start));
        CHECK_CUDA(cudaEventDestroy(stop));
    }

    // =============================================================================
    // Benchmark 2: Shared Memory Stencil
    // =============================================================================
    {
        cudaEvent_t start, stop;
        CHECK_CUDA(cudaEventCreate(&start));
        CHECK_CUDA(cudaEventCreate(&stop));

        CHECK_CUDA(cudaEventRecord(start));
        stencil_1d_shared<<<grid, block>>>(d_output, d_input, N);
        CHECK_CUDA(cudaEventRecord(stop));
        CHECK_CUDA(cudaEventSynchronize(stop));

        float ms = 0;
        CHECK_CUDA(cudaEventElapsedTime(&ms, start, stop));

        // Effective bandwidth: read once + write once
        float bandwidth_gb = (2.0f * bytes) / (ms / 1000.0f) / 1e9f;
        printf("\n[Shared Memory Stencil]\n");
        printf("  Time: %.3f ms\n", ms);
        printf("  Bandwidth: %.2f GB/s\n", bandwidth_gb);

        CHECK_CUDA(cudaMemcpy(h_output, d_output, bytes, cudaMemcpyDeviceToHost));
        verify_stencil(h_output_ref, h_output, N);

        CHECK_CUDA(cudaEventDestroy(start));
        CHECK_CUDA(cudaEventDestroy(stop));
    }

    // =============================================================================
    // Benchmark 3: Read-Only Cache (__ldg)
    // =============================================================================
    {
        cudaEvent_t start, stop;
        CHECK_CUDA(cudaEventCreate(&start));
        CHECK_CUDA(cudaEventCreate(&stop));

        CHECK_CUDA(cudaEventRecord(start));
        stencil_1d_ldg<<<grid, block>>>(d_output, d_input, N);
        CHECK_CUDA(cudaEventRecord(stop));
        CHECK_CUDA(cudaEventSynchronize(stop));

        float ms = 0;
        CHECK_CUDA(cudaEventElapsedTime(&ms, start, stop));

        float bandwidth_gb = (8.0f * bytes) / (ms / 1000.0f) / 1e9f;
        printf("\n[Read-Only Cache (__ldg)]\n");
        printf("  Time: %.3f ms\n", ms);
        printf("  Bandwidth: %.2f GB/s\n", bandwidth_gb);

        CHECK_CUDA(cudaMemcpy(h_output, d_output, bytes, cudaMemcpyDeviceToHost));
        verify_stencil(h_output_ref, h_output, N);

        CHECK_CUDA(cudaEventDestroy(start));
        CHECK_CUDA(cudaEventDestroy(stop));
    }

    // Cleanup
    delete[] h_input;
    delete[] h_output_ref;
    delete[] h_output;
    CHECK_CUDA(cudaFree(d_input));
    CHECK_CUDA(cudaFree(d_output));

    printf("\n✓ 1D stencil demonstration complete!\n");
    return 0;
}
