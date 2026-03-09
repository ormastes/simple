/**
 * @file gpu_kernels.cu
 * @brief GPU kernels for performance testing
 */

#include "../include/gpu_kernels.h"
#include <cuda_runtime.h>
#include <cstdio>

namespace perf_common {
namespace kernels {

// Compute sum for data-dependent addressing
__global__ void compute_sum_kernel(const uint8_t* data, size_t size, uint64_t* result) {
    extern __shared__ uint64_t sdata[];

    int tid = threadIdx.x;
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Init shared memory
    sdata[tid] = 0;

    // Sum multiple elements per thread
    uint64_t local_sum = 0;
    for (size_t i = idx; i < size; i += blockDim.x * gridDim.x) {
        local_sum += data[i];
    }
    sdata[tid] = local_sum;
    __syncthreads();

    // Reduction in shared memory
    for (unsigned int s = blockDim.x / 2; s > 0; s >>= 1) {
        if (tid < s) {
            sdata[tid] += sdata[tid + s];
        }
        __syncthreads();
    }

    // Write block result
    if (tid == 0) {
        atomicAdd((unsigned long long*)result, (unsigned long long)sdata[0]);
    }
}

// XOR transformation
__global__ void xor_transform_kernel(uint8_t* data, size_t size, uint8_t pattern) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < size) {
        // XOR with pattern and rotate bits
        uint8_t val = data[idx];
        val ^= pattern;
        val = (val << 1) | (val >> 7);  // Rotate left by 1
        data[idx] = val;
    }
}

// Fill with pattern
__global__ void pattern_fill_kernel(uint8_t* data, size_t size, uint32_t offset) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < size) {
        // Pattern = (offset + idx) & 0xFF
        data[idx] = (uint8_t)((offset + idx) & 0xFF);
    }
}

// Validate pattern
__global__ void validate_pattern_kernel(const uint8_t* data, size_t size,
                                       uint32_t expected_pattern, uint32_t* errors) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < size) {
        uint8_t expected = (uint8_t)((expected_pattern + idx) & 0xFF);
        if (data[idx] != expected) {
            atomicAdd(errors, 1);
        }
    }
}

// Memory bandwidth test
__global__ void bandwidth_kernel(uint8_t* dst, const uint8_t* src, size_t size) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < size) {
        // Copy for bandwidth test
        dst[idx] = src[idx];
    }
}

// Reduction operators
template<typename T>
struct SumOp {
    __device__ T operator()(T a, T b) const { return a + b; }
};

template<typename T>
struct MaxOp {
    __device__ T operator()(T a, T b) const { return a > b ? a : b; }
};

template<typename T>
struct MinOp {
    __device__ T operator()(T a, T b) const { return a < b ? a : b; }
};

template<typename T, typename Op>
__global__ void reduce_kernel(const T* input, T* output, size_t size, Op op) {
    extern __shared__ uint8_t shared_mem[];
    T* sdata = reinterpret_cast<T*>(shared_mem);

    int tid = threadIdx.x;
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Load and reduce elements
    T local_result = (idx < size) ? input[idx] : T();
    for (size_t i = idx + blockDim.x * gridDim.x; i < size; i += blockDim.x * gridDim.x) {
        local_result = op(local_result, input[i]);
    }
    sdata[tid] = local_result;
    __syncthreads();

    // Reduction in shared memory
    for (unsigned int s = blockDim.x / 2; s > 0; s >>= 1) {
        if (tid < s) {
            sdata[tid] = op(sdata[tid], sdata[tid + s]);
        }
        __syncthreads();
    }

    // Write block result
    if (tid == 0) {
        output[blockIdx.x] = sdata[0];
    }
}

// Explicit instantiations
template __global__ void reduce_kernel<uint32_t, SumOp<uint32_t>>(
    const uint32_t*, uint32_t*, size_t, SumOp<uint32_t>);
template __global__ void reduce_kernel<uint64_t, SumOp<uint64_t>>(
    const uint64_t*, uint64_t*, size_t, SumOp<uint64_t>);
template __global__ void reduce_kernel<float, SumOp<float>>(
    const float*, float*, size_t, SumOp<float>);

// KernelLauncher implementation
cudaError_t KernelLauncher::launch_sum(const uint8_t* data, size_t size,
                                       uint64_t* result, cudaStream_t stream) {
    // Reset result
    cudaMemsetAsync(result, 0, sizeof(uint64_t), stream);

    // Calculate launch configuration
    int threads = 256;
    int blocks = (size + threads - 1) / threads;
    if (blocks > 65536) blocks = 65536;  // Cap at reasonable grid size

    // Launch kernel with shared memory
    size_t shared_mem_size = threads * sizeof(uint64_t);
    compute_sum_kernel<<<blocks, threads, shared_mem_size, stream>>>(data, size, result);

    return cudaGetLastError();
}

cudaError_t KernelLauncher::launch_xor(uint8_t* data, size_t size, uint8_t pattern,
                                       cudaStream_t stream) {
    int threads, blocks;
    get_launch_config(size, blocks, threads);

    xor_transform_kernel<<<blocks, threads, 0, stream>>>(data, size, pattern);
    return cudaGetLastError();
}

cudaError_t KernelLauncher::launch_pattern_fill(uint8_t* data, size_t size,
                                                uint32_t offset, cudaStream_t stream) {
    int threads, blocks;
    get_launch_config(size, blocks, threads);

    pattern_fill_kernel<<<blocks, threads, 0, stream>>>(data, size, offset);
    return cudaGetLastError();
}

cudaError_t KernelLauncher::launch_validate(const uint8_t* data, size_t size,
                                           uint32_t expected_pattern, uint32_t* errors,
                                           cudaStream_t stream) {
    // Reset error counter
    cudaMemsetAsync(errors, 0, sizeof(uint32_t), stream);

    int threads, blocks;
    get_launch_config(size, blocks, threads);

    validate_pattern_kernel<<<blocks, threads, 0, stream>>>(
        data, size, expected_pattern, errors);
    return cudaGetLastError();
}

} // namespace kernels
} // namespace perf_common