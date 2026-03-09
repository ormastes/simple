/**
 * Matrix Transpose with Shared Memory (Part 23)
 *
 * Demonstrates shared memory bank conflict avoidance through padding
 * Compares naive global memory transpose with optimized shared memory approach
 *
 * Key concepts:
 * - Coalesced global memory access
 * - Shared memory bank conflicts
 * - Bank conflict avoidance through padding
 * - Performance comparison
 */

#include <iostream>
#include <cuda_runtime.h>
#include "cuda_utils.h"  // From CudaCustomLib

// =============================================================================
// Naive Transpose (Global Memory Only)
// =============================================================================

/**
 * Naive matrix transpose using global memory only
 *
 * Performance issues:
 * - Non-coalesced writes: Adjacent threads write to rows (stride N)
 * - Result: ~10x slower than optimal
 * - Bandwidth: ~80 GB/s on modern GPUs (vs. ~900 GB/s theoretical)
 */
__global__ void transpose_naive(float* out, const float* in, int N) {
    int x = blockIdx.x * blockDim.x + threadIdx.x;
    int y = blockIdx.y * blockDim.y + threadIdx.y;

    if (x < N && y < N) {
        // Coalesced read, but non-coalesced write!
        // out[x * N + y] means adjacent threads write to different rows
        out[x * N + y] = in[y * N + x];
    }
}

// =============================================================================
// Shared Memory Transpose (With Bank Conflicts)
// =============================================================================

/**
 * Transpose using shared memory without padding
 *
 * Tile size: TILE_DIM × TILE_DIM (e.g., 32×32 = 1,024 threads per block)
 * Shared memory: 32×32 floats = 4,096 bytes (4 KB)
 *
 * Performance issues:
 * - Reading from shared memory: Stride of TILE_DIM (32) → all threads in warp
 *   access same bank → 32-way bank conflict!
 * - Writing to shared memory: Sequential access, no conflicts
 * - Bandwidth: ~400 GB/s (better than naive, but not optimal)
 */
template<int TILE_DIM>
__global__ void transpose_shared_conflicts(float* out, const float* in, int N) {
    __shared__ float tile[TILE_DIM][TILE_DIM];

    int x = blockIdx.x * TILE_DIM + threadIdx.x;
    int y = blockIdx.y * TILE_DIM + threadIdx.y;

    // Coalesced read from global memory into shared memory
    if (x < N && y < N) {
        tile[threadIdx.y][threadIdx.x] = in[y * N + x];
    }
    __syncthreads();

    // Transposed indices for output
    x = blockIdx.y * TILE_DIM + threadIdx.x;
    y = blockIdx.x * TILE_DIM + threadIdx.y;

    // Coalesced write to global memory from transposed shared memory
    // But bank conflicts when reading from tile[threadIdx.x][threadIdx.y]!
    if (x < N && y < N) {
        out[y * N + x] = tile[threadIdx.x][threadIdx.y];
    }
}

// =============================================================================
// Optimized Transpose (Bank Conflict Free)
// =============================================================================

/**
 * Transpose using shared memory WITH padding to avoid bank conflicts
 *
 * Tile size: TILE_DIM × (TILE_DIM + 1) - extra column for padding
 * Shared memory: 32×33 floats = 4,224 bytes (~4 KB)
 *
 * Bank conflict avoidance:
 * - Without padding [32][32]: Accessing column (stride 32) causes all 32 threads
 *   in a warp to hit the same bank → 32-way conflict
 * - With padding [32][33]: Stride becomes 33, which is coprime to 32
 *   Threads access different banks → NO conflicts!
 *
 * Performance:
 * - Bandwidth: ~850 GB/s (near theoretical peak!)
 * - Speedup: ~10x vs naive, ~2x vs shared memory with conflicts
 * - Memory overhead: Only 3% more shared memory (4,224 vs 4,096 bytes)
 */
template<int TILE_DIM>
__global__ void transpose_shared_optimal(float* out, const float* in, int N) {
    // Padding: [TILE_DIM][TILE_DIM + 1] instead of [TILE_DIM][TILE_DIM]
    __shared__ float tile[TILE_DIM][TILE_DIM + 1];

    int x = blockIdx.x * TILE_DIM + threadIdx.x;
    int y = blockIdx.y * TILE_DIM + threadIdx.y;

    // Coalesced read from global memory into shared memory
    if (x < N && y < N) {
        tile[threadIdx.y][threadIdx.x] = in[y * N + x];
    }
    __syncthreads();

    // Transposed indices for output
    x = blockIdx.y * TILE_DIM + threadIdx.x;
    y = blockIdx.x * TILE_DIM + threadIdx.y;

    // Coalesced write to global memory from transposed shared memory
    // NO bank conflicts thanks to padding!
    if (x < N && y < N) {
        out[y * N + x] = tile[threadIdx.x][threadIdx.y];
    }
}

// =============================================================================
// Host Code
// =============================================================================

void verify_transpose(const float* h_out, const float* h_in, int N) {
    bool correct = true;
    int errors = 0;
    const int MAX_ERRORS = 10;

    for (int i = 0; i < N && errors < MAX_ERRORS; i++) {
        for (int j = 0; j < N && errors < MAX_ERRORS; j++) {
            float expected = h_in[j * N + i];  // Transposed
            float actual = h_out[i * N + j];

            if (fabsf(expected - actual) > 1e-5f) {
                if (errors < MAX_ERRORS) {
                    printf("Mismatch at [%d][%d]: expected %.2f, got %.2f\n",
                           i, j, expected, actual);
                }
                correct = false;
                errors++;
            }
        }
    }

    if (correct) {
        printf("✓ Transpose correct!\n");
    } else {
        printf("✗ Transpose incorrect (%d errors shown)\n", std::min(errors, MAX_ERRORS));
    }
}

int main() {
    const int N = 4096;  // 4K × 4K matrix
    const int TILE_DIM = 32;

    size_t bytes = N * N * sizeof(float);
    printf("Matrix size: %d × %d (%.2f MB)\n", N, N, bytes / 1024.0f / 1024.0f);

    // Allocate host memory
    float *h_in = new float[N * N];
    float *h_out = new float[N * N];

    // Initialize input matrix
    for (int i = 0; i < N * N; i++) {
        h_in[i] = static_cast<float>(i % 100);
    }

    // Allocate device memory
    float *d_in, *d_out;
    CHECK_CUDA(cudaMalloc(&d_in, bytes));
    CHECK_CUDA(cudaMalloc(&d_out, bytes));
    CHECK_CUDA(cudaMemcpy(d_in, h_in, bytes, cudaMemcpyHostToDevice));

    dim3 block(TILE_DIM, TILE_DIM);
    dim3 grid((N + TILE_DIM - 1) / TILE_DIM, (N + TILE_DIM - 1) / TILE_DIM);

    // Warm-up
    transpose_shared_optimal<32><<<grid, block>>>(d_out, d_in, N);
    CHECK_CUDA(cudaDeviceSynchronize());

    // =============================================================================
    // Benchmark 1: Naive Transpose
    // =============================================================================
    {
        cudaEvent_t start, stop;
        CHECK_CUDA(cudaEventCreate(&start));
        CHECK_CUDA(cudaEventCreate(&stop));

        CHECK_CUDA(cudaEventRecord(start));
        transpose_naive<<<grid, block>>>(d_out, d_in, N);
        CHECK_CUDA(cudaEventRecord(stop));
        CHECK_CUDA(cudaEventSynchronize(stop));

        float ms = 0;
        CHECK_CUDA(cudaEventElapsedTime(&ms, start, stop));

        float bandwidth_gb = (2.0f * bytes) / (ms / 1000.0f) / 1e9f;
        printf("\n[Naive Transpose]\n");
        printf("  Time: %.3f ms\n", ms);
        printf("  Bandwidth: %.2f GB/s\n", bandwidth_gb);

        CHECK_CUDA(cudaMemcpy(h_out, d_out, bytes, cudaMemcpyDeviceToHost));
        verify_transpose(h_out, h_in, N);

        CHECK_CUDA(cudaEventDestroy(start));
        CHECK_CUDA(cudaEventDestroy(stop));
    }

    // =============================================================================
    // Benchmark 2: Shared Memory with Conflicts
    // =============================================================================
    {
        cudaEvent_t start, stop;
        CHECK_CUDA(cudaEventCreate(&start));
        CHECK_CUDA(cudaEventCreate(&stop));

        CHECK_CUDA(cudaEventRecord(start));
        transpose_shared_conflicts<32><<<grid, block>>>(d_out, d_in, N);
        CHECK_CUDA(cudaEventRecord(stop));
        CHECK_CUDA(cudaEventSynchronize(stop));

        float ms = 0;
        CHECK_CUDA(cudaEventElapsedTime(&ms, start, stop));

        float bandwidth_gb = (2.0f * bytes) / (ms / 1000.0f) / 1e9f;
        printf("\n[Shared Memory with Bank Conflicts]\n");
        printf("  Time: %.3f ms\n", ms);
        printf("  Bandwidth: %.2f GB/s\n", bandwidth_gb);

        CHECK_CUDA(cudaMemcpy(h_out, d_out, bytes, cudaMemcpyDeviceToHost));
        verify_transpose(h_out, h_in, N);

        CHECK_CUDA(cudaEventDestroy(start));
        CHECK_CUDA(cudaEventDestroy(stop));
    }

    // =============================================================================
    // Benchmark 3: Optimized (Bank Conflict Free)
    // =============================================================================
    {
        cudaEvent_t start, stop;
        CHECK_CUDA(cudaEventCreate(&start));
        CHECK_CUDA(cudaEventCreate(&stop));

        CHECK_CUDA(cudaEventRecord(start));
        transpose_shared_optimal<32><<<grid, block>>>(d_out, d_in, N);
        CHECK_CUDA(cudaEventRecord(stop));
        CHECK_CUDA(cudaEventSynchronize(stop));

        float ms = 0;
        CHECK_CUDA(cudaEventElapsedTime(&ms, start, stop));

        float bandwidth_gb = (2.0f * bytes) / (ms / 1000.0f) / 1e9f;
        printf("\n[Optimized (Bank Conflict Free)]\n");
        printf("  Time: %.3f ms\n", ms);
        printf("  Bandwidth: %.2f GB/s\n", bandwidth_gb);

        CHECK_CUDA(cudaMemcpy(h_out, d_out, bytes, cudaMemcpyDeviceToHost));
        verify_transpose(h_out, h_in, N);

        CHECK_CUDA(cudaEventDestroy(start));
        CHECK_CUDA(cudaEventDestroy(stop));
    }

    // Cleanup
    delete[] h_in;
    delete[] h_out;
    CHECK_CUDA(cudaFree(d_in));
    CHECK_CUDA(cudaFree(d_out));

    printf("\n✓ Matrix transpose demonstration complete!\n");
    return 0;
}
