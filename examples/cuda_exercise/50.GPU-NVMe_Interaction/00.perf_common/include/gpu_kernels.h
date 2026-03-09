/**
 * @file gpu_kernels.h
 * @brief GPU kernels for performance testing
 */

#ifndef GPU_KERNELS_H
#define GPU_KERNELS_H

#include <cuda_runtime.h>
#include <cstdint>

namespace perf_common {
namespace kernels {

/**
 * @brief Compute sum of data for data-dependent addressing
 * @param data Input data buffer
 * @param size Size of data in bytes
 * @param result Output sum result
 */
__global__ void compute_sum_kernel(const uint8_t* data, size_t size, uint64_t* result);

/**
 * @brief XOR transformation with pattern
 * @param data Data buffer to transform
 * @param size Size of data in bytes
 * @param pattern XOR pattern to apply
 */
__global__ void xor_transform_kernel(uint8_t* data, size_t size, uint8_t pattern);

/**
 * @brief Generic reduction kernel
 * @tparam T Data type
 * @tparam Op Binary operation type
 * @param input Input data
 * @param output Output result
 * @param size Number of elements
 * @param op Binary operation to apply
 */
template<typename T, typename Op>
__global__ void reduce_kernel(const T* input, T* output, size_t size, Op op);

/**
 * @brief Fill buffer with non-zero pattern
 * @param data Output buffer
 * @param size Size in bytes
 * @param offset Pattern offset
 */
__global__ void pattern_fill_kernel(uint8_t* data, size_t size, uint32_t offset);

/**
 * @brief Validate data matches expected pattern
 * @param data Data to validate
 * @param size Size in bytes
 * @param expected_pattern Expected pattern offset
 * @param errors Output error count
 */
__global__ void validate_pattern_kernel(const uint8_t* data, size_t size,
                                       uint32_t expected_pattern, uint32_t* errors);

/**
 * @brief Streaming read/write for bandwidth measurement
 * @param dst Destination buffer
 * @param src Source buffer
 * @param size Size in bytes
 */
__global__ void bandwidth_kernel(uint8_t* dst, const uint8_t* src, size_t size);

// Helper class for kernel launches with optimal configuration
class KernelLauncher {
public:
    /**
     * @brief Calculate optimal block and grid dimensions
     */
    static void get_launch_config(size_t num_elements, int& blocks, int& threads,
                                  int threads_per_block = 256) {
        threads = threads_per_block;
        blocks = (num_elements + threads_per_block - 1) / threads_per_block;
    }

    /**
     * @brief Launch sum reduction kernel
     */
    static cudaError_t launch_sum(const uint8_t* data, size_t size, uint64_t* result,
                                  cudaStream_t stream = 0);

    /**
     * @brief Launch XOR transform kernel
     */
    static cudaError_t launch_xor(uint8_t* data, size_t size, uint8_t pattern,
                                  cudaStream_t stream = 0);

    /**
     * @brief Launch pattern fill kernel
     */
    static cudaError_t launch_pattern_fill(uint8_t* data, size_t size, uint32_t offset,
                                           cudaStream_t stream = 0);

    /**
     * @brief Launch validation kernel
     */
    static cudaError_t launch_validate(const uint8_t* data, size_t size,
                                       uint32_t expected_pattern, uint32_t* errors,
                                       cudaStream_t stream = 0);
};

} // namespace kernels
} // namespace perf_common

#endif // GPU_KERNELS_H
