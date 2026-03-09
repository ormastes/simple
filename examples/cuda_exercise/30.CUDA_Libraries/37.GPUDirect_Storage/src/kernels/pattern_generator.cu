#include "pattern_generator.h"
#include <cuda_runtime.h>
#include <cstdint>

// Generate sequential byte pattern
__global__ void generate_sequential_pattern(uint8_t* data, size_t size, size_t offset) {
    size_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < size) {
        data[idx] = static_cast<uint8_t>((offset + idx) % 256);
    }
}

// Verify sequential pattern and count mismatches
__global__ void verify_sequential_pattern(const uint8_t* data, size_t size,
                                           size_t offset, int* mismatch_count) {
    size_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < size) {
        uint8_t expected = static_cast<uint8_t>((offset + idx) % 256);
        if (data[idx] != expected) {
            atomicAdd(mismatch_count, 1);
        }
    }
}

// Host wrapper functions

void launchGeneratePattern(uint8_t* d_data, size_t size, size_t offset,
                           cudaStream_t stream) {
    const int block_size = 256;
    const int grid_size = (size + block_size - 1) / block_size;

    generate_sequential_pattern<<<grid_size, block_size, 0, stream>>>(
        d_data, size, offset);
}

int launchVerifyPattern(const uint8_t* d_data, size_t size, size_t offset,
                        cudaStream_t stream) {
    int* d_mismatch_count;
    cudaMalloc(&d_mismatch_count, sizeof(int));
    cudaMemset(d_mismatch_count, 0, sizeof(int));

    const int block_size = 256;
    const int grid_size = (size + block_size - 1) / block_size;

    verify_sequential_pattern<<<grid_size, block_size, 0, stream>>>(
        d_data, size, offset, d_mismatch_count);

    cudaStreamSynchronize(stream);

    int mismatch_count;
    cudaMemcpy(&mismatch_count, d_mismatch_count, sizeof(int),
               cudaMemcpyDeviceToHost);
    cudaFree(d_mismatch_count);

    return mismatch_count;
}
