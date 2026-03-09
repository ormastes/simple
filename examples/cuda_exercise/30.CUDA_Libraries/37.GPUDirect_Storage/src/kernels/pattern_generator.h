#pragma once
#include <cuda_runtime.h>
#include <cstdint>
#include <cstddef>

/**
 * Generate sequential byte pattern in GPU buffer.
 * Pattern: data[i] = (offset + i) % 256
 *
 * @param d_data GPU buffer pointer
 * @param size Buffer size in bytes
 * @param offset Starting offset for pattern generation
 * @param stream CUDA stream (0 for default stream)
 */
void launchGeneratePattern(uint8_t* d_data, size_t size, size_t offset,
                           cudaStream_t stream = 0);

/**
 * Verify sequential byte pattern in GPU buffer.
 * Pattern: data[i] == (offset + i) % 256
 *
 * @param d_data GPU buffer pointer
 * @param size Buffer size in bytes
 * @param offset Starting offset for pattern verification
 * @param stream CUDA stream (0 for default stream)
 * @return Number of mismatched bytes
 */
int launchVerifyPattern(const uint8_t* d_data, size_t size, size_t offset,
                        cudaStream_t stream = 0);
