/**
 * Memory Access Pattern Analysis
 *
 * Comprehensive demonstration of different memory access patterns and their
 * performance characteristics:
 * - Row-major vs column-major access
 * - Aligned vs misaligned access
 * - Vectorized access patterns
 * - 2D array access with pitch
 *
 * Key Concepts:
 * - Cache line utilization
 * - Transaction efficiency
 * - Alignment requirements
 * - Pitch/stride considerations for 2D arrays
 */

#include <cuda_runtime.h>
#include <stdio.h>
#include "cuda_utils.h"

#define BLOCK_DIM_X 32
#define BLOCK_DIM_Y 8
#define MATRIX_SIZE 4096
#define ITERATIONS 100

// ============================================================================
// 2D Array Access Patterns
// ============================================================================

/**
 * Row-major access (coalesced)
 * Threads in a warp access consecutive columns in the same row
 * Perfect coalescing: warp accesses row[0..31] in one transaction
 */
__global__ void row_major_access(const float* __restrict__ matrix,
                                  float* __restrict__ output,
                                  int width, int height) {
    int col = blockIdx.x * blockDim.x + threadIdx.x;
    int row = blockIdx.y * blockDim.y + threadIdx.y;

    if (row < height && col < width) {
        // Coalesced: consecutive threads access consecutive memory
        int idx = row * width + col;
        output[idx] = matrix[idx] * 2.0f;
    }
}

/**
 * Column-major access (non-coalesced)
 * Threads in a warp access different rows in the same column
 * Poor coalescing: each thread accesses strided memory (stride = width)
 */
__global__ void column_major_access(const float* __restrict__ matrix,
                                     float* __restrict__ output,
                                     int width, int height) {
    int col = blockIdx.x * blockDim.x + threadIdx.x;
    int row = blockIdx.y * blockDim.y + threadIdx.y;

    if (row < height && col < width) {
        // Non-coalesced: warp accesses column[0..31] (stride = width)
        int idx = col * height + row;
        output[idx] = matrix[idx] * 2.0f;
    }
}

/**
 * Diagonal access (poor coalescing)
 * Each thread accesses a diagonal element
 * Strided access pattern, poor cache utilization
 */
__global__ void diagonal_access(const float* __restrict__ matrix,
                                 float* __restrict__ output,
                                 int width, int height) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;

    if (tid < min(width, height)) {
        // Diagonal: matrix[0,0], [1,1], [2,2], ...
        // Stride = width + 1, poor coalescing
        int idx = tid * width + tid;
        output[tid] = matrix[idx] * 2.0f;
    }
}

// ============================================================================
// Alignment Patterns
// ============================================================================

/**
 * Aligned access - starts at 128-byte boundary
 * Optimal performance, perfect cache line utilization
 */
__global__ void aligned_access(const float* __restrict__ data,
                                float* __restrict__ output, int n) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    if (tid < n) {
        // Assuming data pointer is 128-byte aligned
        output[tid] = data[tid] * 2.0f;
    }
}

/**
 * Misaligned access - offset from natural alignment
 * Reduced efficiency, may require extra transactions
 */
__global__ void misaligned_access(const float* __restrict__ data,
                                   float* __restrict__ output,
                                   int n, int offset) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    if (tid < n - offset) {
        // Offset breaks alignment, reduces coalescing
        output[tid] = data[tid + offset] * 2.0f;
    }
}

// ============================================================================
// Vectorized Access Patterns
// ============================================================================

/**
 * Scalar access - load one float at a time
 * Standard 4-byte transactions
 */
__global__ void scalar_access(const float* __restrict__ input,
                               float* __restrict__ output, int n) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    if (tid < n) {
        output[tid] = input[tid] * 2.0f;
    }
}

/**
 * Vectorized float2 access - load two floats at once
 * 8-byte transactions, potentially better bandwidth
 */
__global__ void vectorized_float2_access(const float2* __restrict__ input,
                                          float2* __restrict__ output, int n) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    if (tid < n) {
        float2 val = input[tid];
        val.x *= 2.0f;
        val.y *= 2.0f;
        output[tid] = val;
    }
}

/**
 * Vectorized float4 access - load four floats at once
 * 16-byte transactions, maximum single-instruction bandwidth
 */
__global__ void vectorized_float4_access(const float4* __restrict__ input,
                                          float4* __restrict__ output, int n) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    if (tid < n) {
        float4 val = input[tid];
        val.x *= 2.0f;
        val.y *= 2.0f;
        val.z *= 2.0f;
        val.w *= 2.0f;
        output[tid] = val;
    }
}

// ============================================================================
// Pitched 2D Memory Access
// ============================================================================

/**
 * Pitched memory access using cudaMallocPitch
 * Ensures proper alignment for each row
 */
__global__ void pitched_2d_access(const float* __restrict__ matrix,
                                   float* __restrict__ output,
                                   int width, int height, size_t pitch) {
    int col = blockIdx.x * blockDim.x + threadIdx.x;
    int row = blockIdx.y * blockDim.y + threadIdx.y;

    if (row < height && col < width) {
        // Use pitch for proper aligned access
        const float* input_row = (const float*)((const char*)matrix + row * pitch);
        float* output_row = (float*)((char*)output + row * pitch);
        output_row[col] = input_row[col] * 2.0f;
    }
}

// ============================================================================
// Benchmark Functions
// ============================================================================

template<typename KernelFunc, typename... Args>
float benchmark_2d_kernel(const char* name, KernelFunc kernel,
                           dim3 grid, dim3 block,
                           int width, int height, Args... args) {
    CudaTimer timer;

    // Warmup
    for (int i = 0; i < 10; i++) {
        kernel<<<grid, block>>>(args...);
    }
    CHECK_CUDA(cudaDeviceSynchronize());

    // Benchmark
    timer.start();
    for (int i = 0; i < ITERATIONS; i++) {
        kernel<<<grid, block>>>(args...);
    }
    timer.stop();

    float time_ms = timer.elapsed_ms() / ITERATIONS;
    float bandwidth = (2 * width * height * sizeof(float) / 1e9) / (time_ms / 1000.0f);

    printf("%-35s: %.3f ms, %6.2f GB/s\n", name, time_ms, bandwidth);
    return bandwidth;
}

template<typename KernelFunc, typename... Args>
float benchmark_1d_kernel(const char* name, KernelFunc kernel,
                           int n, int blocks, Args... args) {
    CudaTimer timer;

    // Warmup
    for (int i = 0; i < 10; i++) {
        kernel<<<blocks, 256>>>(args...);
    }
    CHECK_CUDA(cudaDeviceSynchronize());

    // Benchmark
    timer.start();
    for (int i = 0; i < ITERATIONS; i++) {
        kernel<<<blocks, 256>>>(args...);
    }
    timer.stop();

    float time_ms = timer.elapsed_ms() / ITERATIONS;
    float bandwidth = (2 * n * sizeof(float) / 1e9) / (time_ms / 1000.0f);

    printf("%-35s: %.3f ms, %6.2f GB/s\n", name, time_ms, bandwidth);
    return bandwidth;
}

// ============================================================================
// Main Demonstration
// ============================================================================

int main() {
    cudaDeviceProp prop;
    CHECK_CUDA(cudaGetDeviceProperties(&prop, 0));

    printf("=== Memory Access Pattern Analysis ===\n");
    printf("Device: %s\n", prop.name);
    printf("Matrix Size: %dx%d (%.2f MB)\n\n",
           MATRIX_SIZE, MATRIX_SIZE,
           MATRIX_SIZE * MATRIX_SIZE * sizeof(float) / 1e6);

    // Allocate 2D matrices
    float *d_matrix, *d_output;
    CHECK_CUDA(cudaMalloc(&d_matrix, MATRIX_SIZE * MATRIX_SIZE * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, MATRIX_SIZE * MATRIX_SIZE * sizeof(float)));
    CHECK_CUDA(cudaMemset(d_matrix, 1, MATRIX_SIZE * MATRIX_SIZE * sizeof(float)));

    dim3 block(BLOCK_DIM_X, BLOCK_DIM_Y);
    dim3 grid((MATRIX_SIZE + BLOCK_DIM_X - 1) / BLOCK_DIM_X,
              (MATRIX_SIZE + BLOCK_DIM_Y - 1) / BLOCK_DIM_Y);

    // 2D Access Patterns
    printf("2D Array Access Patterns:\n");
    printf("%-35s  %s  %s\n", "Pattern", "Time(ms)", "BW(GB/s)");
    printf("%-35s  %s  %s\n", "-------", "--------", "--------");

    float row_bw = benchmark_2d_kernel("Row-major (coalesced)", row_major_access,
                                        grid, block, MATRIX_SIZE, MATRIX_SIZE,
                                        d_matrix, d_output, MATRIX_SIZE, MATRIX_SIZE);

    float col_bw = benchmark_2d_kernel("Column-major (non-coalesced)", column_major_access,
                                        grid, block, MATRIX_SIZE, MATRIX_SIZE,
                                        d_matrix, d_output, MATRIX_SIZE, MATRIX_SIZE);

    benchmark_2d_kernel("Diagonal (poor coalescing)", diagonal_access,
                        dim3((MATRIX_SIZE + 255) / 256), dim3(256),
                        MATRIX_SIZE, MATRIX_SIZE,
                        d_matrix, d_output, MATRIX_SIZE, MATRIX_SIZE);

    printf("  → Row-major is %.2fx faster than column-major\n\n", row_bw / col_bw);

    // Alignment Patterns
    const int n = 16 * 1024 * 1024;
    float *d_data1d, *d_output1d;
    CHECK_CUDA(cudaMalloc(&d_data1d, n * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output1d, n * sizeof(float)));

    int blocks = (n + 255) / 256;

    printf("Alignment Patterns:\n");
    printf("%-35s  %s  %s\n", "Pattern", "Time(ms)", "BW(GB/s)");
    printf("%-35s  %s  %s\n", "-------", "--------", "--------");

    float aligned_bw = benchmark_1d_kernel("Aligned (offset=0)", aligned_access,
                                            n, blocks, d_data1d, d_output1d, n);

    float misaligned1_bw = benchmark_1d_kernel("Misaligned (offset=1)", misaligned_access,
                                                n, blocks, d_data1d, d_output1d, n, 1);

    float misaligned17_bw = benchmark_1d_kernel("Misaligned (offset=17)", misaligned_access,
                                                 n, blocks, d_data1d, d_output1d, n, 17);

    printf("  → Misalignment reduces efficiency by %.1f%%\n\n",
           (1.0f - misaligned17_bw / aligned_bw) * 100.0f);

    // Vectorized Access
    printf("Vectorized Access Patterns:\n");
    printf("%-35s  %s  %s\n", "Pattern", "Time(ms)", "BW(GB/s)");
    printf("%-35s  %s  %s\n", "-------", "--------", "--------");

    benchmark_1d_kernel("Scalar (1 float)", scalar_access,
                        n, blocks, d_data1d, d_output1d, n);

    benchmark_1d_kernel("Vectorized (float2)", vectorized_float2_access,
                        n / 2, blocks / 2,
                        reinterpret_cast<float2*>(d_data1d),
                        reinterpret_cast<float2*>(d_output1d), n / 2);

    benchmark_1d_kernel("Vectorized (float4)", vectorized_float4_access,
                        n / 4, blocks / 4,
                        reinterpret_cast<float4*>(d_data1d),
                        reinterpret_cast<float4*>(d_output1d), n / 4);

    printf("\n");

    // Pitched memory
    float *d_pitched_matrix, *d_pitched_output;
    size_t pitch;
    CHECK_CUDA(cudaMallocPitch(&d_pitched_matrix, &pitch,
                               MATRIX_SIZE * sizeof(float), MATRIX_SIZE));
    CHECK_CUDA(cudaMallocPitch(&d_pitched_output, &pitch,
                               MATRIX_SIZE * sizeof(float), MATRIX_SIZE));

    printf("Pitched 2D Memory (size=%dx%d, pitch=%zu bytes):\n",
           MATRIX_SIZE, MATRIX_SIZE, pitch);
    benchmark_2d_kernel("Pitched access (optimized)", pitched_2d_access,
                        grid, block, MATRIX_SIZE, MATRIX_SIZE,
                        d_pitched_matrix, d_pitched_output,
                        MATRIX_SIZE, MATRIX_SIZE, pitch);

    printf("\n✓ Memory access pattern analysis complete!\n");
    printf("\nKey Takeaways:\n");
    printf("  1. Row-major access is essential for coalescing\n");
    printf("  2. Alignment matters - misalignment reduces efficiency\n");
    printf("  3. Vectorized loads can improve bandwidth utilization\n");
    printf("  4. Use cudaMallocPitch for 2D arrays to ensure alignment\n");

    printf("\nProfiling Recommendations:\n");
    printf("  ncu --metrics gld_transactions,gld_efficiency,l1tex__t_bytes_pipe_lsu_mem_global_op_ld.sum \\\n");
    printf("      ./24_Memory_Coalescing_And_Bank_Conflicts_memory_patterns\n");

    // Cleanup
    CHECK_CUDA(cudaFree(d_matrix));
    CHECK_CUDA(cudaFree(d_output));
    CHECK_CUDA(cudaFree(d_data1d));
    CHECK_CUDA(cudaFree(d_output1d));
    CHECK_CUDA(cudaFree(d_pitched_matrix));
    CHECK_CUDA(cudaFree(d_pitched_output));

    return 0;
}
