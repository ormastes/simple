/**
 * @file layout_swizzle.cuh
 * @brief Memory layout helpers for row-major, column-major, and padded strides
 *
 * Provides stride calculation and coordinate mapping for various tensor layouts
 * used in GEMM and attention kernels.
 */
#pragma once

#include <cuda_runtime.h>

namespace transformer {

/**
 * @brief Memory layout enumeration
 *
 * Specifies the memory layout for tensor storage, affecting how multi-dimensional
 * indices are mapped to linear memory addresses.
 */
enum class Layout {
    RowMajor,   ///< Standard C row-major layout
    ColMajor,   ///< Fortran-style column-major layout
    Col32       ///< 32-column padded layout for Tensor Core compatibility
};

/**
 * @brief Calculate linear index for row-major layout
 * @param[in] row Row index
 * @param[in] col Column index
 * @param[in] num_cols Number of columns (stride)
 * @return Linear memory index
 */
__host__ __device__ __forceinline__
int row_major_idx(int row, int col, int num_cols) {
    return row * num_cols + col;
}

/**
 * @brief Calculate linear index for column-major layout
 * @param[in] row Row index
 * @param[in] col Column index
 * @param[in] num_rows Number of rows (stride)
 * @return Linear memory index
 */
__host__ __device__ __forceinline__
int col_major_idx(int row, int col, int num_rows) {
    return col * num_rows + row;
}

/**
 * @brief Calculate padded stride for Col32 layout
 *
 * Rounds up a dimension to the nearest multiple of 32, as required by
 * Tensor Core WMMA operations.
 *
 * @param[in] dim Original dimension
 * @return Padded dimension (rounded up to multiple of 32)
 */
__host__ __device__ __forceinline__
int col32_padded(int dim) {
    return ((dim + 31) / 32) * 32;
}

/**
 * @brief Calculate linear index for Col32 layout
 *
 * Col32 layout groups columns into blocks of 32, interleaving rows within each
 * block. This layout is optimized for Tensor Core memory access patterns.
 *
 * @param[in] row Row index
 * @param[in] col Column index
 * @param[in] num_rows Number of rows in the matrix
 * @return Linear memory index in Col32 layout
 */
__host__ __device__ __forceinline__
int col32_idx(int row, int col, int num_rows) {
    int col_block = col / 32;
    int col_within = col % 32;
    return col_block * (num_rows * 32) + row * 32 + col_within;
}

/**
 * @brief Generic stride calculator for 3D tensors
 *
 * Computes linear offsets from 3D indices using configurable strides,
 * supporting batch, row, and column dimensions.
 */
struct StrideHelper {
    int stride0;  ///< Outermost stride (batch)
    int stride1;  ///< Middle stride (row or head)
    int stride2;  ///< Innermost stride (column or sequence)

    /**
     * @brief Compute linear index from 3D coordinates
     * @param[in] i0 Outermost index (batch)
     * @param[in] i1 Middle index (row/head)
     * @param[in] i2 Innermost index (column/sequence)
     * @return Linear memory offset
     */
    __host__ __device__ __forceinline__
    int operator()(int i0, int i1, int i2) const {
        return i0 * stride0 + i1 * stride1 + i2 * stride2;
    }
};

/**
 * @brief Create stride helper for [B, M, N] row-major tensor
 * @param[in] M Number of rows per batch
 * @param[in] N Number of columns per row
 * @return StrideHelper configured for row-major [B, M, N] layout
 */
__host__ __device__ __forceinline__
StrideHelper make_row_major_3d(int M, int N) {
    return StrideHelper{M * N, N, 1};
}

/**
 * @brief Swizzle function for shared memory bank conflict avoidance
 *
 * XOR-based swizzle that remaps linear shared memory indices to avoid
 * bank conflicts during warp-level access patterns. Uses bits 4-6 of the
 * index to XOR with the lower 3 bits.
 *
 * @param[in] idx Linear shared memory index
 * @return Swizzled index with reduced bank conflicts
 */
__device__ __forceinline__
int smem_swizzle(int idx) {
    return idx ^ ((idx >> 4) & 0x7);
}

} // namespace transformer
