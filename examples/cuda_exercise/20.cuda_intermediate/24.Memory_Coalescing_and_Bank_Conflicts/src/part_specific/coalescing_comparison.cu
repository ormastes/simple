/**
 * Comparison: Module 23 (Shared Memory) vs Module 24 (Coalescing Optimized)
 *
 * This demonstration compares the performance of kernels from module 23
 * with the improved versions in module 24 that focus on memory coalescing.
 *
 * Comparisons:
 * 1. Matrix Multiplication: Naive → Tiled → Coalescing Optimized → Vectorized
 * 2. Reduction: Basic → Vectorized → Warp Shuffle
 * 3. Performance metrics and analysis
 */

#include <cuda_runtime.h>
#include <stdio.h>
#include "cuda_utils.h"

// Include improved kernels (Module 24 versions with coalescing optimizations)
#include "../kernels/matrix_multiply.cu"
#include "../kernels/vector_ops.cu"

#define TILE_SIZE 16
#define BLOCK_SIZE 256

// ============================================================================
// Matrix Multiplication Benchmark
// ============================================================================

void benchmark_matmul(int M, int N, int K) {
    printf("=== Matrix Multiplication Comparison ===\n");
    printf("Matrix Size: %dx%d × %dx%d\n", M, K, K, N);
    printf("Memory: A=%.2f MB, B=%.2f MB, C=%.2f MB\n\n",
           M * K * sizeof(float) / 1e6,
           K * N * sizeof(float) / 1e6,
           M * N * sizeof(float) / 1e6);

    // Allocate matrices
    float *h_A, *h_B, *h_C, *h_C_ref;
    float *d_A, *d_B, *d_C;

    CHECK_CUDA(cudaMallocHost(&h_A, M * K * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_B, K * N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_C, M * N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_C_ref, M * N * sizeof(float)));

    // Initialize
    for (int i = 0; i < M * K; i++) h_A[i] = (i % 100) * 0.01f;
    for (int i = 0; i < K * N; i++) h_B[i] = (i % 100) * 0.01f;

    // Compute reference on CPU (small subset for verification)
    if (M <= 128 && N <= 128) {
        for (int i = 0; i < M; i++) {
            for (int j = 0; j < N; j++) {
                float sum = 0.0f;
                for (int k = 0; k < K; k++) {
                    sum += h_A[i * K + k] * h_B[k * N + j];
                }
                h_C_ref[i * N + j] = sum;
            }
        }
    }

    CHECK_CUDA(cudaMalloc(&d_A, M * K * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_B, K * N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_C, M * N * sizeof(float)));

    CHECK_CUDA(cudaMemcpy(d_A, h_A, M * K * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_B, h_B, K * N * sizeof(float), cudaMemcpyHostToDevice));

    dim3 block(TILE_SIZE, TILE_SIZE);
    dim3 grid((N + TILE_SIZE - 1) / TILE_SIZE, (M + TILE_SIZE - 1) / TILE_SIZE);

    CudaTimer timer;

    printf("%-40s  %s  %s\n", "Kernel", "Time(ms)", "GFLOPS");
    printf("%-40s  %s  %s\n", "------", "--------", "------");

    // 1. Naive (Module 23 baseline)
    timer.start();
    matmul_naive<<<grid, block>>>(d_A, d_B, d_C, M, N, K);
    timer.stop();
    CHECK_KERNEL_LAUNCH();

    float time_naive = timer.elapsed_ms();
    float gflops_naive = (2.0f * M * N * K) / (time_naive * 1e6);
    printf("%-40s  %7.3f  %7.2f\n", "Naive (No Optimization)", time_naive, gflops_naive);

    // 2. Tiled with padding (Module 23)
    timer.start();
    matmul_tiled_padded<TILE_SIZE><<<grid, block>>>(d_A, d_B, d_C, M, N, K);
    timer.stop();
    CHECK_KERNEL_LAUNCH();

    float time_tiled = timer.elapsed_ms();
    float gflops_tiled = (2.0f * M * N * K) / (time_tiled * 1e6);
    printf("%-40s  %7.3f  %7.2f  (%.1fx speedup)\n",
           "Tiled + Padding (Module 23)", time_tiled, gflops_tiled,
           time_naive / time_tiled);

    // 3. Coalescing optimized (Module 24)
    timer.start();
    matmul_coalescing_optimized<TILE_SIZE><<<grid, block>>>(d_A, d_B, d_C, M, N, K);
    timer.stop();
    CHECK_KERNEL_LAUNCH();

    float time_coalesced = timer.elapsed_ms();
    float gflops_coalesced = (2.0f * M * N * K) / (time_coalesced * 1e6);
    printf("%-40s  %7.3f  %7.2f  (%.1fx speedup)\n",
           "Coalescing Optimized (Module 24)", time_coalesced, gflops_coalesced,
           time_naive / time_coalesced);

    // 4. Prefetch double buffer (Module 24 advanced)
    timer.start();
    matmul_prefetch_double_buffer<TILE_SIZE><<<grid, block>>>(d_A, d_B, d_C, M, N, K);
    timer.stop();
    CHECK_KERNEL_LAUNCH();

    float time_prefetch = timer.elapsed_ms();
    float gflops_prefetch = (2.0f * M * N * K) / (time_prefetch * 1e6);
    printf("%-40s  %7.3f  %7.2f  (%.1fx speedup)\n",
           "Prefetch Double Buffer (Module 24)", time_prefetch, gflops_prefetch,
           time_naive / time_prefetch);

    // Verify correctness (if reference computed)
    if (M <= 128 && N <= 128) {
        CHECK_CUDA(cudaMemcpy(h_C, d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost));
        bool correct = true;
        for (int i = 0; i < M * N && correct; i++) {
            if (fabs(h_C[i] - h_C_ref[i]) > 1e-2f) {
                printf("Error at index %d: GPU=%f, CPU=%f\n", i, h_C[i], h_C_ref[i]);
                correct = false;
            }
        }
        if (correct) {
            printf("\n✓ All results verified correct!\n");
        }
    }

    printf("\n");

    cudaFreeHost(h_A);
    cudaFreeHost(h_B);
    cudaFreeHost(h_C);
    cudaFreeHost(h_C_ref);
    cudaFree(d_A);
    cudaFree(d_B);
    cudaFree(d_C);
}

// ============================================================================
// Reduction Benchmark
// ============================================================================

void benchmark_reduction(int N) {
    printf("=== Reduction Comparison ===\n");
    printf("Array Size: %d elements (%.2f MB)\n\n", N, N * sizeof(float) / 1e6);

    float *h_input, *h_output;
    float *d_input, *d_output;

    int num_blocks = (N + BLOCK_SIZE - 1) / BLOCK_SIZE;

    CHECK_CUDA(cudaMallocHost(&h_input, N * sizeof(float)));
    CHECK_CUDA(cudaMallocHost(&h_output, num_blocks * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_input, N * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, num_blocks * sizeof(float)));

    // Initialize with ones for easy verification
    for (int i = 0; i < N; i++) {
        h_input[i] = 1.0f;
    }
    CHECK_CUDA(cudaMemcpy(d_input, h_input, N * sizeof(float), cudaMemcpyHostToDevice));

    CudaTimer timer;

    printf("%-40s  %s  %s\n", "Kernel", "Time(ms)", "Bandwidth(GB/s)");
    printf("%-40s  %s  %s\n", "------", "--------", "--------------");

    // 1. Vectorized reduction (Module 24)
    timer.start();
    reduction_vectorized<BLOCK_SIZE><<<num_blocks / 4, BLOCK_SIZE>>>(d_input, d_output, N);
    timer.stop();
    CHECK_KERNEL_LAUNCH();

    float time_vec = timer.elapsed_ms();
    float bw_vec = (N * sizeof(float) / 1e9) / (time_vec / 1000.0f);
    printf("%-40s  %7.3f  %7.2f\n", "Vectorized (Module 24)", time_vec, bw_vec);

    // 2. Warp shuffle reduction (Module 24)
    timer.start();
    reduction_warp_shuffle<BLOCK_SIZE><<<num_blocks, BLOCK_SIZE>>>(d_input, d_output, N);
    timer.stop();
    CHECK_KERNEL_LAUNCH();

    float time_shuffle = timer.elapsed_ms();
    float bw_shuffle = (N * sizeof(float) / 1e9) / (time_shuffle / 1000.0f);
    printf("%-40s  %7.3f  %7.2f  (%.1fx faster)\n",
           "Warp Shuffle (Module 24)", time_shuffle, bw_shuffle,
           time_vec / time_shuffle);

    // Verify
    CHECK_CUDA(cudaMemcpy(h_output, d_output, num_blocks * sizeof(float), cudaMemcpyDeviceToHost));
    float result = 0.0f;
    for (int i = 0; i < num_blocks; i++) {
        result += h_output[i];
    }

    if (fabs(result - N) < N * 1e-5f) {
        printf("\n✓ Reduction result verified: %.0f (expected: %d)\n", result, N);
    } else {
        printf("\n✗ Reduction result incorrect: %.0f (expected: %d)\n", result, N);
    }

    printf("\n");

    cudaFreeHost(h_input);
    cudaFreeHost(h_output);
    cudaFree(d_input);
    cudaFree(d_output);
}

// ============================================================================
// Main
// ============================================================================

int main() {
    cudaDeviceProp prop;
    CHECK_CUDA(cudaGetDeviceProperties(&prop, 0));

    printf("╔══════════════════════════════════════════════════════════════╗\n");
    printf("║   Module 23 vs Module 24 Performance Comparison            ║\n");
    printf("╚══════════════════════════════════════════════════════════════╝\n\n");

    printf("Device: %s\n", prop.name);
    printf("Compute Capability: %d.%d\n", prop.major, prop.minor);
    printf("Memory Bus Width: %d bits\n\n", prop.memoryBusWidth);

    // Matrix multiplication comparison
    benchmark_matmul(1024, 1024, 1024);

    printf("─────────────────────────────────────────────────────────────\n\n");

    // Reduction comparison
    benchmark_reduction(16 * 1024 * 1024);

    printf("═════════════════════════════════════════════════════════════\n\n");

    printf("Key Improvements in Module 24:\n");
    printf("  1. Explicit coalescing analysis for all memory accesses\n");
    printf("  2. Vectorized loads using float4 (16-byte transactions)\n");
    printf("  3. __ldg() for read-only cache utilization\n");
    printf("  4. Warp-level primitives (__shfl_down_sync)\n");
    printf("  5. Bank conflict elimination via +1 padding\n");
    printf("  6. Double buffering for latency hiding\n\n");

    printf("Expected Speedups:\n");
    printf("  - Naive → Tiled: 20-40x\n");
    printf("  - Tiled → Coalescing Optimized: 1.2-1.5x\n");
    printf("  - Coalescing → Prefetch: 1.1-1.3x\n");
    printf("  - Basic Reduction → Warp Shuffle: 1.2-1.5x\n\n");

    printf("Profiling Commands:\n");
    printf("  ncu --metrics gld_efficiency,gld_transactions ./coalescing_comparison\n");
    printf("  ncu --metrics shared_efficiency,l1tex__data_bank_conflicts_pipe_lsu_mem_shared_op_ld.sum ./coalescing_comparison\n\n");

    return 0;
}
