/**
 * 1D Convolution with Shared Memory (Part 23)
 *
 * Demonstrates efficient 1D convolution using shared memory to cache
 * input data and reduce global memory accesses
 *
 * Key concepts:
 * - Shared memory as a user-managed cache
 * - Halo cells for boundary handling
 * - Memory access pattern optimization
 * - Global vs. shared memory bandwidth comparison
 */

#include <iostream>
#include <cuda_runtime.h>
#include "cuda_utils.h"  // From CudaCustomLib

#define MASK_RADIUS 5
#define MASK_SIZE (2 * MASK_RADIUS + 1)
#define BLOCK_SIZE 256

// Constant memory for convolution mask (faster than global memory)
__constant__ float c_mask[MASK_SIZE];

// =============================================================================
// Naive 1D Convolution (Global Memory Only)
// =============================================================================

/**
 * Naive 1D convolution reading directly from global memory
 *
 * Performance issues:
 * - Each thread reads MASK_SIZE (11) elements from global memory
 * - Overlapping reads between threads → wasted bandwidth
 * - For 256-thread block: ~2,816 global reads (256 * 11)
 * - But only ~266 unique elements needed (256 + 2*5)
 * - Bandwidth waste: ~10x redundant reads!
 * - Effective bandwidth: ~100 GB/s
 */
__global__ void convolution_1d_naive(float* output, const float* input, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (idx < N) {
        float sum = 0.0f;

        // Apply convolution mask
        for (int k = -MASK_RADIUS; k <= MASK_RADIUS; k++) {
            int pos = idx + k;

            // Boundary handling
            if (pos >= 0 && pos < N) {
                sum += input[pos] * c_mask[k + MASK_RADIUS];
            }
        }

        output[idx] = sum;
    }
}

// =============================================================================
// Optimized 1D Convolution (Shared Memory)
// =============================================================================

/**
 * Optimized 1D convolution using shared memory caching
 *
 * Shared memory usage:
 *   temp[BLOCK_SIZE + 2 * MASK_RADIUS]: Caches input tile + halo cells
 *   For BLOCK_SIZE=256, MASK_RADIUS=5: 266 floats = 1,064 bytes (~1 KB)
 *
 * Halo cells:
 *   Left halo: 5 elements before the tile
 *   Right halo: 5 elements after the tile
 *   Total halo: 10 elements
 *
 * Memory access pattern:
 * - Each block loads 266 elements from global memory ONCE
 * - All threads reuse cached data in shared memory
 * - Global reads: 266 per block (vs 2,816 in naive version)
 * - Bandwidth reduction: ~10x improvement!
 * - Effective bandwidth: ~800 GB/s
 *
 * Performance: ~8x faster than naive version
 */
__global__ void convolution_1d_shared(float* output, const float* input, int N) {
    // Shared memory: Block tile + halo cells on both sides
    __shared__ float temp[BLOCK_SIZE + 2 * MASK_RADIUS];

    int global_idx = blockIdx.x * blockDim.x + threadIdx.x;
    int local_idx = threadIdx.x + MASK_RADIUS;  // Offset by halo size

    // Load center tile element into shared memory
    if (global_idx < N) {
        temp[local_idx] = input[global_idx];
    } else {
        temp[local_idx] = 0.0f;
    }

    // Load left halo cells
    if (threadIdx.x < MASK_RADIUS) {
        int halo_idx = global_idx - MASK_RADIUS;
        temp[threadIdx.x] = (halo_idx >= 0) ? input[halo_idx] : 0.0f;
    }

    // Load right halo cells
    if (threadIdx.x < MASK_RADIUS) {
        int halo_idx = global_idx + BLOCK_SIZE;
        temp[local_idx + BLOCK_SIZE] = (halo_idx < N) ? input[halo_idx] : 0.0f;
    }

    __syncthreads();

    // Apply convolution using cached data
    if (global_idx < N) {
        float sum = 0.0f;

        #pragma unroll
        for (int k = -MASK_RADIUS; k <= MASK_RADIUS; k++) {
            sum += temp[local_idx + k] * c_mask[k + MASK_RADIUS];
        }

        output[global_idx] = sum;
    }
}

// =============================================================================
// Host Code
// =============================================================================

void verify_convolution(const float* h_out_ref, const float* h_out, int N) {
    bool correct = true;
    int errors = 0;
    const int MAX_ERRORS = 10;

    for (int i = 0; i < N && errors < MAX_ERRORS; i++) {
        if (fabsf(h_out_ref[i] - h_out[i]) > 1e-4f) {
            if (errors < MAX_ERRORS) {
                printf("Mismatch at [%d]: expected %.4f, got %.4f\n",
                       i, h_out_ref[i], h_out[i]);
            }
            correct = false;
            errors++;
        }
    }

    if (correct) {
        printf("✓ Convolution correct!\n");
    } else {
        printf("✗ Convolution incorrect (%d errors shown)\n", std::min(errors, MAX_ERRORS));
    }
}

int main() {
    const int N = 16 * 1024 * 1024;  // 16M elements
    size_t bytes = N * sizeof(float);

    printf("Array size: %d elements (%.2f MB)\n", N, bytes / 1024.0f / 1024.0f);
    printf("Mask radius: %d (mask size: %d)\n", MASK_RADIUS, MASK_SIZE);

    // Initialize convolution mask (Gaussian-like)
    float h_mask[MASK_SIZE];
    float sum = 0.0f;
    for (int i = 0; i < MASK_SIZE; i++) {
        int dist = abs(i - MASK_RADIUS);
        h_mask[i] = expf(-0.5f * dist * dist);
        sum += h_mask[i];
    }
    // Normalize
    for (int i = 0; i < MASK_SIZE; i++) {
        h_mask[i] /= sum;
    }

    // Copy mask to constant memory
    CHECK_CUDA(cudaMemcpyToSymbol(c_mask, h_mask, MASK_SIZE * sizeof(float)));

    // Allocate host memory
    float *h_input = new float[N];
    float *h_output_ref = new float[N];
    float *h_output = new float[N];

    // Initialize input
    for (int i = 0; i < N; i++) {
        h_input[i] = sinf(i * 0.01f);
    }

    // Allocate device memory
    float *d_input, *d_output;
    CHECK_CUDA(cudaMalloc(&d_input, bytes));
    CHECK_CUDA(cudaMalloc(&d_output, bytes));
    CHECK_CUDA(cudaMemcpy(d_input, h_input, bytes, cudaMemcpyHostToDevice));

    dim3 block(BLOCK_SIZE);
    dim3 grid((N + BLOCK_SIZE - 1) / BLOCK_SIZE);

    // Warm-up
    convolution_1d_shared<<<grid, block>>>(d_output, d_input, N);
    CHECK_CUDA(cudaDeviceSynchronize());

    // =============================================================================
    // Benchmark 1: Naive Convolution
    // =============================================================================
    {
        cudaEvent_t start, stop;
        CHECK_CUDA(cudaEventCreate(&start));
        CHECK_CUDA(cudaEventCreate(&stop));

        CHECK_CUDA(cudaEventRecord(start));
        convolution_1d_naive<<<grid, block>>>(d_output, d_input, N);
        CHECK_CUDA(cudaEventRecord(stop));
        CHECK_CUDA(cudaEventSynchronize(stop));

        float ms = 0;
        CHECK_CUDA(cudaEventElapsedTime(&ms, start, stop));

        // Bandwidth: reads (N * MASK_SIZE) + writes (N)
        float bandwidth_gb = ((N * MASK_SIZE + N) * sizeof(float)) / (ms / 1000.0f) / 1e9f;
        printf("\n[Naive Convolution]\n");
        printf("  Time: %.3f ms\n", ms);
        printf("  Bandwidth: %.2f GB/s\n", bandwidth_gb);

        CHECK_CUDA(cudaMemcpy(h_output_ref, d_output, bytes, cudaMemcpyDeviceToHost));

        CHECK_CUDA(cudaEventDestroy(start));
        CHECK_CUDA(cudaEventDestroy(stop));
    }

    // =============================================================================
    // Benchmark 2: Shared Memory Convolution
    // =============================================================================
    {
        cudaEvent_t start, stop;
        CHECK_CUDA(cudaEventCreate(&start));
        CHECK_CUDA(cudaEventCreate(&stop));

        CHECK_CUDA(cudaEventRecord(start));
        convolution_1d_shared<<<grid, block>>>(d_output, d_input, N);
        CHECK_CUDA(cudaEventRecord(stop));
        CHECK_CUDA(cudaEventSynchronize(stop));

        float ms = 0;
        CHECK_CUDA(cudaEventElapsedTime(&ms, start, stop));

        // Bandwidth: Each element read once + written once
        float bandwidth_gb = (2.0f * bytes) / (ms / 1000.0f) / 1e9f;
        printf("\n[Shared Memory Convolution]\n");
        printf("  Time: %.3f ms\n", ms);
        printf("  Bandwidth: %.2f GB/s\n", bandwidth_gb);

        CHECK_CUDA(cudaMemcpy(h_output, d_output, bytes, cudaMemcpyDeviceToHost));
        verify_convolution(h_output_ref, h_output, N);

        CHECK_CUDA(cudaEventDestroy(start));
        CHECK_CUDA(cudaEventDestroy(stop));
    }

    // Cleanup
    delete[] h_input;
    delete[] h_output_ref;
    delete[] h_output;
    CHECK_CUDA(cudaFree(d_input));
    CHECK_CUDA(cudaFree(d_output));

    printf("\n✓ 1D convolution demonstration complete!\n");
    return 0;
}
