/**
 * @file vector_io.cu
 * @brief Compilation unit for vector_io utilities
 */
#include "vector_io.cuh"

// Force template instantiation
namespace transformer {
template __device__ void vectorized_copy<4>(float*, const float*, int);
template __device__ void vectorized_copy<2>(float*, const float*, int);
} // namespace transformer
