/**
 * @file sum_kernel.cu
 * @brief CUDA kernel implementation for sum_kernel
 *
 * @author Yoon, Jonghyun
 * @date 2025-10-25
 */

// sum_kernel.cu - GPU kernel to sum 4KB data block
#include <cuda_runtime.h>
#include <cstdint>

/**
 * Reduce sum kernel using shared memory
 *
 * This kernel sums a 4KB block (1024 uint32_t values) using parallel reduction.
 * Each thread block reduces a portion, final reduction happens in block 0.
 */
__global__ void sum_4kb_block_kernel(const uint32_t* data, uint32_t* result, uint32_t num_elements) {
    extern __shared__ uint32_t sdata[];

    unsigned int tid = threadIdx.x;
    unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;

    // Load data into shared memory
    sdata[tid] = (i < num_elements) ? data[i] : 0;
    __syncthreads();

    // Parallel reduction in shared memory
    for (unsigned int s = blockDim.x / 2; s > 0; s >>= 1) {
        if (tid < s) {
            sdata[tid] += sdata[tid + s];
        }
        __syncthreads();
    }

    // Write block result to global memory
    if (tid == 0) {
        atomicAdd(result, sdata[0]);
    }
}

/**
 * Host-callable function to sum 4KB of data
 *
 * @param data Device pointer to 4KB buffer (1024 uint32_t values)
 * @param result Device pointer to result
 * @param stream CUDA stream for async execution
 */
extern "C" void launch_sum_4kb(const void* data, uint32_t* result, cudaStream_t stream) {
    const uint32_t num_elements = 1024;  // 4KB / sizeof(uint32_t)
    const uint32_t threads = 256;
    const uint32_t blocks = (num_elements + threads - 1) / threads;

    // Zero out result
    cudaMemsetAsync(result, 0, sizeof(uint32_t), stream);

    // Launch reduction kernel
    sum_4kb_block_kernel<<<blocks, threads, threads * sizeof(uint32_t), stream>>>(
        reinterpret_cast<const uint32_t*>(data),
        result,
        num_elements
    );
}

/**
 * Synchronous version for testing
 */
extern "C" uint32_t sum_4kb_sync(const void* data) {
    uint32_t h_result = 0;
    uint32_t* d_result;
    cudaMalloc(&d_result, sizeof(uint32_t));

    launch_sum_4kb(data, d_result, 0);
    cudaDeviceSynchronize();

    cudaMemcpy(&h_result, d_result, sizeof(uint32_t), cudaMemcpyDeviceToHost);
    cudaFree(d_result);

    return h_result;
}
