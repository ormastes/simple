/**
 * @file sum_kernel.h
 * @brief GPU kernel to sum 4KB data block
 */
#pragma once
#include <cuda_runtime.h>
#include <cstdint>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Launch GPU kernel to sum 4KB of data (async)
 * @param data Device pointer to 4KB buffer
 * @param result Device pointer to uint32_t result
 * @param stream CUDA stream for async execution
 */
void launch_sum_4kb(const void* data, uint32_t* result, cudaStream_t stream);

/**
 * @brief Synchronously sum 4KB of data on GPU
 * @param data Device pointer to 4KB buffer
 * @return Sum of all uint32_t values
 */
uint32_t sum_4kb_sync(const void* data);

#ifdef __cplusplus
}
#endif
