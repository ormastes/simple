/* bench_sum_squares_cuda.cu — CUDA GPU sum-of-squares for JIT comparison
 *
 * Same computation as bench_2d_tiered_jit.spl hot_compute:
 *   sum(i*i for i in 0..n) where n = 100000
 *
 * Computes on GPU using parallel reduction.
 * Build: nvcc -O2 -o bench_sum_squares_cuda bench_sum_squares_cuda.cu
 */
#include <stdio.h>
#include <stdint.h>
#include <time.h>

#define WORK_SIZE      100000
#define WARMUP_CALLS   128
#define MEASURED_CALLS 2000
#define BLOCK_SIZE     256

static double now_seconds(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

__global__ void sum_squares_kernel(int64_t n, int64_t *result) {
    __shared__ int64_t sdata[BLOCK_SIZE];
    int tid = threadIdx.x;
    int64_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    int64_t stride = gridDim.x * blockDim.x;

    int64_t local_sum = 0;
    for (int64_t i = idx; i < n; i += stride) {
        local_sum += i * i;
    }
    sdata[tid] = local_sum;
    __syncthreads();

    for (int s = BLOCK_SIZE / 2; s > 0; s >>= 1) {
        if (tid < s) sdata[tid] += sdata[tid + s];
        __syncthreads();
    }
    if (tid == 0) atomicAdd((unsigned long long*)result, (unsigned long long)sdata[0]);
}

int64_t gpu_hot_compute(int64_t n, int64_t *d_result) {
    cudaMemset(d_result, 0, sizeof(int64_t));
    int blocks = (n + BLOCK_SIZE - 1) / BLOCK_SIZE;
    if (blocks > 256) blocks = 256;
    sum_squares_kernel<<<blocks, BLOCK_SIZE>>>(n, d_result);
    int64_t h_result;
    cudaMemcpy(&h_result, d_result, sizeof(int64_t), cudaMemcpyDeviceToHost);
    return h_result;
}

int64_t cpu_hot_compute(int64_t n) {
    int64_t sum = 0;
    for (int64_t i = 0; i < n; i++) sum += i * i;
    return sum;
}

int main(void) {
    printf("=== Sum-of-Squares Comparison: C CPU vs CUDA GPU ===\n");
    printf("  WORK_SIZE=%d, WARMUP=%d, MEASURED=%d\n\n", WORK_SIZE, WARMUP_CALLS, MEASURED_CALLS);

    int64_t *d_result;
    cudaMalloc(&d_result, sizeof(int64_t));

    /* Warmup GPU */
    gpu_hot_compute(WORK_SIZE, d_result);
    cudaDeviceSynchronize();

    /* --- C CPU (gcc -O2) --- */
    printf("--- C CPU (-O2 optimized) ---\n");
    double t0 = now_seconds();
    volatile int64_t sink = 0;
    for (int i = 0; i < MEASURED_CALLS; i++) {
        sink += cpu_hot_compute(WORK_SIZE);
    }
    double t1 = now_seconds();
    double cpu_s = t1 - t0;
    double cpu_per_call_us = cpu_s * 1e6 / MEASURED_CALLS;
    printf("  %d calls in %.6f s (%.3f us/call)\n", MEASURED_CALLS, cpu_s, cpu_per_call_us);
    printf("  Result: %ld\n", (long)cpu_hot_compute(WORK_SIZE));

    /* --- CUDA GPU --- */
    printf("\n--- CUDA GPU (parallel reduction) ---\n");
    double t2 = now_seconds();
    for (int i = 0; i < MEASURED_CALLS; i++) {
        gpu_hot_compute(WORK_SIZE, d_result);
    }
    cudaDeviceSynchronize();
    double t3 = now_seconds();
    double gpu_s = t3 - t2;
    double gpu_per_call_us = gpu_s * 1e6 / MEASURED_CALLS;
    int64_t gpu_result = gpu_hot_compute(WORK_SIZE, d_result);
    printf("  %d calls in %.6f s (%.3f us/call)\n", MEASURED_CALLS, gpu_s, gpu_per_call_us);
    printf("  Result: %ld\n", (long)gpu_result);

    /* --- Summary --- */
    printf("\n--- Summary (same work: sum(i*i) for i in 0..%d) ---\n", WORK_SIZE);
    printf("  C CPU (-O2):     %.3f us/call\n", cpu_per_call_us);
    printf("  CUDA GPU:        %.3f us/call\n", gpu_per_call_us);
    if (gpu_per_call_us > 0 && cpu_per_call_us > 0) {
        if (cpu_per_call_us > gpu_per_call_us)
            printf("  GPU speedup:     %.2fx faster than C CPU\n", cpu_per_call_us / gpu_per_call_us);
        else
            printf("  CPU faster:      %.2fx (kernel launch overhead dominates at this size)\n", gpu_per_call_us / cpu_per_call_us);
    }
    printf("  Simple interp:   ~297000.0 us/call (from JIT benchmark)\n");
    printf("  Simple Cranelift: ~500.0 us/call (from JIT benchmark)\n");

    cudaFree(d_result);
    return 0;
}
