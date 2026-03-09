/**
 * Memory Coalescing Demonstration
 *
 * Demonstrates the impact of different memory access patterns on bandwidth:
 * - Perfectly coalesced access (consecutive addresses)
 * - Strided access (non-consecutive with fixed stride)
 * - Misaligned access (offset from natural alignment)
 *
 * Optimizations Applied:
 * - Sequential thread access for perfect coalescing
 * - Vectorized loads where applicable
 * - Proper alignment consideration
 */

#include <cuda_runtime.h>
#include <stdio.h>
#include "cuda_utils.h"

#define BLOCK_SIZE 256
#define NUM_ELEMENTS (16 * 1024 * 1024)  // 16M elements = 64 MB
#define WARMUP_ITERATIONS 10
#define BENCHMARK_ITERATIONS 100

// ============================================================================
// Kernel Implementations
// ============================================================================

/**
 * Perfectly coalesced access - consecutive threads access consecutive memory
 * Each warp accesses 128 bytes in a single transaction (32 threads × 4 bytes)
 */
__global__ void coalesced_access(const float* __restrict__ input,
                                  float* __restrict__ output, int n) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    if (tid < n) {
        // Perfect coalescing: thread i accesses input[i]
        output[tid] = input[tid] * 2.0f;
    }
}

/**
 * Strided access - threads access memory with fixed stride
 * Causes multiple memory transactions per warp (poor coalescing)
 */
__global__ void strided_access(const float* __restrict__ input,
                                float* __restrict__ output, int n, int stride) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    int idx = tid * stride;
    if (idx < n) {
        // Poor coalescing: thread i accesses input[i * stride]
        // For stride=2, warp needs 2 transactions; stride=8 needs 8 transactions
        output[tid] = input[idx] * 2.0f;
    }
}

/**
 * Misaligned access - offset from natural alignment boundary
 * Reduces coalescing efficiency even for sequential access
 */
__global__ void misaligned_access(const float* __restrict__ input,
                                   float* __restrict__ output, int n, int offset) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    if (tid + offset < n) {
        // Misaligned coalescing: thread i accesses input[i + offset]
        // If offset is not multiple of 32, crosses cache line boundaries
        output[tid] = input[tid + offset] * 2.0f;
    }
}

/**
 * Vectorized coalesced access using float4
 * Loads 16 bytes per thread instead of 4, better utilizing memory bandwidth
 */
__global__ void vectorized_coalesced_access(const float4* __restrict__ input,
                                             float4* __restrict__ output, int n) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    if (tid < n) {
        // Load 16 bytes at once (4 floats)
        float4 val = input[tid];
        val.x *= 2.0f;
        val.y *= 2.0f;
        val.z *= 2.0f;
        val.w *= 2.0f;
        output[tid] = val;
    }
}

// ============================================================================
// Benchmark Harness
// ============================================================================

struct BenchmarkResult {
    float time_ms;
    float bandwidth_gb_s;
    float efficiency_percent;
};

template<typename KernelFunc, typename... Args>
BenchmarkResult benchmark_kernel(const char* name, KernelFunc kernel,
                                  int n, int blocks, Args... args) {
    CudaTimer timer;

    // Warmup
    for (int i = 0; i < WARMUP_ITERATIONS; i++) {
        kernel<<<blocks, BLOCK_SIZE>>>(args...);
    }
    CHECK_CUDA(cudaDeviceSynchronize());

    // Benchmark
    timer.start();
    for (int i = 0; i < BENCHMARK_ITERATIONS; i++) {
        kernel<<<blocks, BLOCK_SIZE>>>(args...);
    }
    timer.stop();

    BenchmarkResult result;
    result.time_ms = timer.elapsed_ms() / BENCHMARK_ITERATIONS;

    // Bandwidth calculation: 2 arrays (read + write) × size × iterations
    size_t bytes_transferred = 2 * n * sizeof(float);
    result.bandwidth_gb_s = (bytes_transferred / 1e9) / (result.time_ms / 1000.0f);

    // Efficiency calculation (baseline against achieved bandwidth)
    // Using first iteration as reference for relative comparison
    static float baseline_bandwidth = 0.0f;
    if (baseline_bandwidth == 0.0f) {
        baseline_bandwidth = result.bandwidth_gb_s;
    }
    result.efficiency_percent = (result.bandwidth_gb_s / baseline_bandwidth) * 100.0f;

    printf("%-30s: %.3f ms, %6.2f GB/s (%5.1f%% efficiency)\n",
           name, result.time_ms, result.bandwidth_gb_s, result.efficiency_percent);

    return result;
}

// ============================================================================
// Main Demonstration
// ============================================================================

int main() {
    // Print device info
    cudaDeviceProp prop;
    CHECK_CUDA(cudaGetDeviceProperties(&prop, 0));

    printf("=== Memory Coalescing Benchmark ===\n");
    printf("Device: %s\n", prop.name);
    printf("Memory Bus Width: %d bits\n", prop.memoryBusWidth);
    printf("Elements: %d (%.2f MB)\n\n", NUM_ELEMENTS, NUM_ELEMENTS * sizeof(float) / 1e6);

    // Allocate device memory
    float *d_input, *d_output;
    CHECK_CUDA(cudaMalloc(&d_input, NUM_ELEMENTS * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_output, NUM_ELEMENTS * sizeof(float)));

    // Initialize with dummy data
    CHECK_CUDA(cudaMemset(d_input, 1, NUM_ELEMENTS * sizeof(float)));

    int blocks = (NUM_ELEMENTS + BLOCK_SIZE - 1) / BLOCK_SIZE;

    printf("Access Pattern Comparison:\n");
    printf("%-30s  %s  %s  %s\n", "Pattern", "Time(ms)", "BW(GB/s)", "Efficiency");
    printf("%-30s  %s  %s  %s\n", "-------", "--------", "--------", "----------");

    // 1. Perfect coalescing - baseline
    benchmark_kernel("Coalesced (baseline)", coalesced_access,
                     NUM_ELEMENTS, blocks, d_input, d_output, NUM_ELEMENTS);

    // 2. Vectorized coalescing - should match or exceed baseline
    benchmark_kernel("Vectorized (float4)", vectorized_coalesced_access,
                     NUM_ELEMENTS, blocks / 4,
                     reinterpret_cast<float4*>(d_input),
                     reinterpret_cast<float4*>(d_output),
                     NUM_ELEMENTS / 4);

    // 3. Strided access with varying strides
    benchmark_kernel("Strided (stride=2)", strided_access,
                     NUM_ELEMENTS / 2, blocks / 2,
                     d_input, d_output, NUM_ELEMENTS, 2);

    benchmark_kernel("Strided (stride=4)", strided_access,
                     NUM_ELEMENTS / 4, blocks / 4,
                     d_input, d_output, NUM_ELEMENTS, 4);

    benchmark_kernel("Strided (stride=8)", strided_access,
                     NUM_ELEMENTS / 8, blocks / 8,
                     d_input, d_output, NUM_ELEMENTS, 8);

    benchmark_kernel("Strided (stride=16)", strided_access,
                     NUM_ELEMENTS / 16, blocks / 16,
                     d_input, d_output, NUM_ELEMENTS, 16);

    // 4. Misaligned access
    benchmark_kernel("Misaligned (offset=1)", misaligned_access,
                     NUM_ELEMENTS - 1, blocks,
                     d_input, d_output, NUM_ELEMENTS, 1);

    benchmark_kernel("Misaligned (offset=17)", misaligned_access,
                     NUM_ELEMENTS - 17, blocks,
                     d_input, d_output, NUM_ELEMENTS, 17);

    printf("\n✓ Memory coalescing demonstration complete!\n");
    printf("\nKey Observations:\n");
    printf("  - Coalesced access achieves near-peak bandwidth\n");
    printf("  - Vectorized loads can improve efficiency further\n");
    printf("  - Strided access scales linearly with stride (2x stride = 2x slowdown)\n");
    printf("  - Misalignment reduces efficiency by 10-20%%\n");

    printf("\nProfiling Suggestion:\n");
    printf("  Run: ncu --metrics gld_efficiency,gst_efficiency,gld_transactions ./24_Memory_Coalescing_And_Bank_Conflicts_coalescing_demo\n");

    // Cleanup
    CHECK_CUDA(cudaFree(d_input));
    CHECK_CUDA(cudaFree(d_output));

    return 0;
}
