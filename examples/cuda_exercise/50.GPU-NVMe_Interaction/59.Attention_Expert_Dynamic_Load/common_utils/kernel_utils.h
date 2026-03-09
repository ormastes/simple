/**
 * @file kernel_utils.h
 * @brief Shared CUDA kernel utilities for Module 59
 */

#pragma once

namespace module59 {
namespace kernel {

/**
 * @brief Write a single integer value to device memory
 * @param device_ptr Pointer to device memory
 * @param value Integer value to write
 */
void writeIntegerToDevice(int* device_ptr, int value);

} // namespace kernel
} // namespace module59