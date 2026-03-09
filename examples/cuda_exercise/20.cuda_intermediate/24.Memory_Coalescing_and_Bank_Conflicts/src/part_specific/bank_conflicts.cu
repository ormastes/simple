/**
 * Shared Memory Bank Conflicts Demonstration
 *
 * Demonstrates how different access patterns affect shared memory performance:
 * - No conflicts: Linear sequential access
 * - 2-way conflicts: Stride-2 access pattern
 * - 8-way conflicts: Stride-8 access pattern
 * - 32-way conflicts: Worst case - all threads access same bank
 * - Padding optimization: Eliminating conflicts in transpose operations
 *
 * Bank Organization:
 * - 32 banks in shared memory
 * - Each bank is 4 bytes wide
 * - Bank ID = (address / 4) % 32
 * - Accessing same bank from multiple threads causes serialization
 */

#include <cuda_runtime.h>
#include <stdio.h>
#include "cuda_utils.h"

#define BLOCK_SIZE 256
#define SHARED_SIZE 1024
#define TILE_SIZE 32
#define ITERATIONS 1000

// ============================================================================
// Bank Conflict Kernels
// ============================================================================

/**
 * No bank conflicts - linear sequential access
 * Thread i accesses sdata[i] -> Bank (i % 32)
 * All 32 threads in a warp access different banks
 */
__global__ void no_bank_conflicts() {
    __shared__ float sdata[SHARED_SIZE];

    int tid = threadIdx.x;

    // Initialize with linear access (no conflicts)
    sdata[tid] = static_cast<float>(tid);
    __syncthreads();

    // Perform repeated accesses to measure performance
    float sum = 0.0f;
    #pragma unroll 8
    for (int i = 0; i < ITERATIONS; i++) {
        sum += sdata[tid];  // Perfect - each thread different bank
    }

    // Store result to prevent optimization
    if (tid == 0) {
        sdata[0] = sum;
    }
}

/**
 * 2-way bank conflicts - stride 2 access
 * Thread i accesses sdata[i * 2] -> Bank ((i * 2) % 32)
 * Threads 0 and 16 both access bank 0, causing 2-way conflict
 */
__global__ void twoway_bank_conflicts() {
    __shared__ float sdata[SHARED_SIZE];

    int tid = threadIdx.x;

    // Initialize with stride-2 access
    if (tid * 2 < SHARED_SIZE) {
        sdata[tid * 2] = static_cast<float>(tid);
    }
    __syncthreads();

    // Repeated stride-2 accesses (2-way conflicts)
    float sum = 0.0f;
    #pragma unroll 8
    for (int i = 0; i < ITERATIONS; i++) {
        if (tid * 2 < SHARED_SIZE) {
            sum += sdata[tid * 2];
        }
    }

    if (tid == 0) {
        sdata[0] = sum;
    }
}

/**
 * 8-way bank conflicts - stride 8 access
 * Thread i accesses sdata[(i * 8) % SHARED_SIZE]
 * 8 threads map to the same bank, serialized into 8 transactions
 */
__global__ void eightway_bank_conflicts() {
    __shared__ float sdata[SHARED_SIZE];

    int tid = threadIdx.x;

    // Initialize with stride-8 pattern
    int idx = (tid * 8) % SHARED_SIZE;
    sdata[idx] = static_cast<float>(tid);
    __syncthreads();

    // Repeated stride-8 accesses (8-way conflicts)
    float sum = 0.0f;
    #pragma unroll 8
    for (int i = 0; i < ITERATIONS; i++) {
        sum += sdata[idx];
    }

    if (tid == 0) {
        sdata[0] = sum;
    }
}

/**
 * 32-way bank conflicts (worst case) - all threads access same bank
 * Thread i accesses sdata[i * 32]
 * All 32 threads in warp access bank 0, serialized into 32 transactions
 */
__global__ void worst_case_bank_conflicts() {
    __shared__ float sdata[SHARED_SIZE];

    int tid = threadIdx.x;

    // All threads access indices that map to bank 0
    int idx = tid * 32;  // Addresses: 0, 32, 64, ... all map to bank 0
    if (idx < SHARED_SIZE) {
        sdata[idx] = static_cast<float>(tid);
    }
    __syncthreads();

    // Repeated worst-case accesses
    float sum = 0.0f;
    #pragma unroll 8
    for (int i = 0; i < ITERATIONS; i++) {
        if (idx < SHARED_SIZE) {
            sum += sdata[idx];
        }
    }

    if (tid == 0) {
        sdata[0] = sum;
    }
}

/**
 * Padding optimization for matrix transpose
 * Using [TILE_SIZE][TILE_SIZE + 1] to avoid bank conflicts
 *
 * Without padding: Transposed access causes conflicts
 * With padding: Extra column shifts bank mapping, eliminating conflicts
 */
__global__ void transpose_no_padding(const float* __restrict__ input,
                                      float* __restrict__ output,
                                      int width, int height) {
    __shared__ float tile[TILE_SIZE][TILE_SIZE];  // No padding

    int x = blockIdx.x * TILE_SIZE + threadIdx.x;
    int y = blockIdx.y * TILE_SIZE + threadIdx.y;

    // Load tile from global memory (coalesced)
    if (x < width && y < height) {
        tile[threadIdx.y][threadIdx.x] = input[y * width + x];
    }
    __syncthreads();

    // Transpose coordinates
    x = blockIdx.y * TILE_SIZE + threadIdx.x;
    y = blockIdx.x * TILE_SIZE + threadIdx.y;

    // Store transposed tile (bank conflicts here!)
    if (x < height && y < width) {
        output[y * height + x] = tile[threadIdx.x][threadIdx.y];
    }
}

__global__ void transpose_with_padding(const float* __restrict__ input,
                                        float* __restrict__ output,
                                        int width, int height) {
    __shared__ float tile[TILE_SIZE][TILE_SIZE + 1];  // +1 padding

    int x = blockIdx.x * TILE_SIZE + threadIdx.x;
    int y = blockIdx.y * TILE_SIZE + threadIdx.y;

    // Load tile from global memory (coalesced)
    if (x < width && y < height) {
        tile[threadIdx.y][threadIdx.x] = input[y * width + x];
    }
    __syncthreads();

    // Transpose coordinates
    x = blockIdx.y * TILE_SIZE + threadIdx.x;
    y = blockIdx.x * TILE_SIZE + threadIdx.y;

    // Store transposed tile (NO bank conflicts due to padding!)
    if (x < height && y < width) {
        output[y * height + x] = tile[threadIdx.x][threadIdx.y];
    }
}

// ============================================================================
// Benchmark Harness
// ============================================================================

void benchmark_kernel(const char* name, void (*kernel)(), int iterations = 100) {
    CudaTimer timer;

    // Warmup
    for (int i = 0; i < 10; i++) {
        kernel<<<1, BLOCK_SIZE>>>();
    }
    CHECK_CUDA(cudaDeviceSynchronize());

    // Benchmark
    timer.start();
    for (int i = 0; i < iterations; i++) {
        kernel<<<1, BLOCK_SIZE>>>();
    }
    timer.stop();

    printf("%-40s: %8.3f ms\n", name, timer.elapsed_ms());
}

void benchmark_transpose(const char* name,
                          void (*kernel)(const float*, float*, int, int),
                          float* d_input, float* d_output,
                          int width, int height) {
    CudaTimer timer;

    dim3 block(TILE_SIZE, TILE_SIZE);
    dim3 grid((width + TILE_SIZE - 1) / TILE_SIZE,
              (height + TILE_SIZE - 1) / TILE_SIZE);

    // Warmup
    for (int i = 0; i < 10; i++) {
        kernel<<<grid, block>>>(d_input, d_output, width, height);
    }
    CHECK_CUDA(cudaDeviceSynchronize());

    // Benchmark
    timer.start();
    for (int i = 0; i < 100; i++) {
        kernel<<<grid, block>>>(d_input, d_output, width, height);
    }
    timer.stop();

    float time_ms = timer.elapsed_ms() / 100.0f;
    float bandwidth = (2 * width * height * sizeof(float) / 1e9) / (time_ms / 1000.0f);

    printf("%-40s: %8.3f ms, %6.2f GB/s\n", name, time_ms, bandwidth);
}

// ============================================================================
// Main Demonstration
// ============================================================================

int main() {
    cudaDeviceProp prop;
    CHECK_CUDA(cudaGetDeviceProperties(&prop, 0));

    printf("=== Shared Memory Bank Conflicts Benchmark ===\n");
    printf("Device: %s\n", prop.name);
    printf("Shared Memory per Block: %zu KB\n", prop.sharedMemPerBlock / 1024);
    printf("Shared Memory Banks: 32\n");
    printf("Bank Width: 4 bytes\n\n");

    printf("Bank Conflict Comparison (lower is better):\n");
    printf("%-40s  %s\n", "Access Pattern", "Time (ms)");
    printf("%-40s  %s\n", "---------------", "----------");

    // Benchmark different conflict patterns
    benchmark_kernel("No Bank Conflicts (linear)", no_bank_conflicts);
    benchmark_kernel("2-way Bank Conflicts (stride 2)", twoway_bank_conflicts);
    benchmark_kernel("8-way Bank Conflicts (stride 8)", eightway_bank_conflicts);
    benchmark_kernel("32-way Conflicts (worst case)", worst_case_bank_conflicts);

    printf("\n");

    // Transpose benchmarks
    const int matrix_size = 2048;
    float *d_input, *d_output;
    CHECK_CUDA(cudaMalloc(&d_input, matrix_size * matrix_size * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, matrix_size * matrix_size * sizeof(float)));
    CHECK_CUDA(cudaMemset(d_input, 1, matrix_size * matrix_size * sizeof(float)));

    printf("Matrix Transpose (%dx%d):\n", matrix_size, matrix_size);
    benchmark_transpose("Transpose (no padding - conflicts)", transpose_no_padding,
                        d_input, d_output, matrix_size, matrix_size);
    benchmark_transpose("Transpose (with padding - optimized)", transpose_with_padding,
                        d_input, d_output, matrix_size, matrix_size);

    printf("\n✓ Bank conflict demonstration complete!\n");
    printf("\nKey Observations:\n");
    printf("  - Linear access (no conflicts) is fastest\n");
    printf("  - Performance degrades linearly with conflict degree\n");
    printf("  - 32-way conflicts can be 32x slower than conflict-free\n");
    printf("  - Padding (+1 column) eliminates transpose conflicts\n");

    printf("\nProfiling Suggestion:\n");
    printf("  Run: ncu --metrics shared_load_transactions_per_request,shared_store_transactions_per_request ./24_Memory_Coalescing_And_Bank_Conflicts_bank_conflicts\n");

    CHECK_CUDA(cudaFree(d_input));
    CHECK_CUDA(cudaFree(d_output));

    return 0;
}
