/**
 * @file bandwidth_test.cu
 * @brief STREAM-like GPU memory bandwidth benchmarks.
 *
 * Implements four standard bandwidth tests (Copy, Scale, Add, Triad)
 * inspired by the STREAM benchmark, adapted for GPU global memory.
 * Results are reported in GB/s.
 */
#include "profiling/bandwidth_test.h"
#include <cuda_runtime.h>
#include <cstdio>
#include <cmath>

namespace opt79 {

/// @brief Copy kernel: c[i] = a[i]
__global__ void bw_copy_kernel(float* __restrict__ c, const float* __restrict__ a, size_t n) {
    size_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) c[idx] = a[idx];
}

/// @brief Scale kernel: b[i] = scalar * c[i]
__global__ void bw_scale_kernel(float* __restrict__ b, const float* __restrict__ c,
                                 float scalar, size_t n) {
    size_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) b[idx] = scalar * c[idx];
}

/// @brief Add kernel: c[i] = a[i] + b[i]
__global__ void bw_add_kernel(float* __restrict__ c, const float* __restrict__ a,
                               const float* __restrict__ b, size_t n) {
    size_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) c[idx] = a[idx] + b[idx];
}

/// @brief Triad kernel: a[i] = b[i] + scalar * c[i]
__global__ void bw_triad_kernel(float* __restrict__ a, const float* __restrict__ b,
                                 const float* __restrict__ c, float scalar, size_t n) {
    size_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) a[idx] = b[idx] + scalar * c[idx];
}

BandwidthResult run_bandwidth_test(size_t num_elements, int num_trials) {
    size_t bytes = num_elements * sizeof(float);
    float scalar = 3.0f;

    float *d_a, *d_b, *d_c;
    cudaMalloc(&d_a, bytes);
    cudaMalloc(&d_b, bytes);
    cudaMalloc(&d_c, bytes);

    int threads = 256;
    int blocks = (num_elements + threads - 1) / threads;

    // Warm up and initialize
    bw_triad_kernel<<<blocks, threads>>>(d_a, d_b, d_c, 1.0f, num_elements);
    cudaDeviceSynchronize();

    cudaEvent_t start, stop;
    cudaEventCreate(&start);
    cudaEventCreate(&stop);

    BandwidthResult result = {0, 0, 0, 0};

    // Copy: read a, write c => 2 * bytes
    {
        float best_ms = 1e9f;
        for (int t = 0; t < num_trials; ++t) {
            cudaEventRecord(start);
            bw_copy_kernel<<<blocks, threads>>>(d_c, d_a, num_elements);
            cudaEventRecord(stop);
            cudaEventSynchronize(stop);
            float ms;
            cudaEventElapsedTime(&ms, start, stop);
            if (ms < best_ms) best_ms = ms;
        }
        result.copy_gbps = 2.0 * bytes / (best_ms * 1e-3) / 1e9;
    }

    // Scale: read c, write b => 2 * bytes
    {
        float best_ms = 1e9f;
        for (int t = 0; t < num_trials; ++t) {
            cudaEventRecord(start);
            bw_scale_kernel<<<blocks, threads>>>(d_b, d_c, scalar, num_elements);
            cudaEventRecord(stop);
            cudaEventSynchronize(stop);
            float ms;
            cudaEventElapsedTime(&ms, start, stop);
            if (ms < best_ms) best_ms = ms;
        }
        result.scale_gbps = 2.0 * bytes / (best_ms * 1e-3) / 1e9;
    }

    // Add: read a, read b, write c => 3 * bytes
    {
        float best_ms = 1e9f;
        for (int t = 0; t < num_trials; ++t) {
            cudaEventRecord(start);
            bw_add_kernel<<<blocks, threads>>>(d_c, d_a, d_b, num_elements);
            cudaEventRecord(stop);
            cudaEventSynchronize(stop);
            float ms;
            cudaEventElapsedTime(&ms, start, stop);
            if (ms < best_ms) best_ms = ms;
        }
        result.add_gbps = 3.0 * bytes / (best_ms * 1e-3) / 1e9;
    }

    // Triad: read b, read c, write a => 3 * bytes
    {
        float best_ms = 1e9f;
        for (int t = 0; t < num_trials; ++t) {
            cudaEventRecord(start);
            bw_triad_kernel<<<blocks, threads>>>(d_a, d_b, d_c, scalar, num_elements);
            cudaEventRecord(stop);
            cudaEventSynchronize(stop);
            float ms;
            cudaEventElapsedTime(&ms, start, stop);
            if (ms < best_ms) best_ms = ms;
        }
        result.triad_gbps = 3.0 * bytes / (best_ms * 1e-3) / 1e9;
    }

    cudaEventDestroy(start);
    cudaEventDestroy(stop);
    cudaFree(d_a);
    cudaFree(d_b);
    cudaFree(d_c);

    return result;
}

void print_bandwidth_result(const BandwidthResult& r) {
    printf("=== GPU Bandwidth Test ===\n");
    printf("Copy:  %8.2f GB/s\n", r.copy_gbps);
    printf("Scale: %8.2f GB/s\n", r.scale_gbps);
    printf("Add:   %8.2f GB/s\n", r.add_gbps);
    printf("Triad: %8.2f GB/s\n", r.triad_gbps);
    printf("==========================\n");
}

}  // namespace opt79
