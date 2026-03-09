/**
 * Cooperative Groups Kernels Header
 *
 * Declares all cooperative groups enhanced kernels for Module 23.
 * These kernels improve upon Module 25's dynamic parallelism with
 * better synchronization primitives and performance.
 */

#pragma once

#include <cuda_runtime.h>

// ============================================================================
// Reduction Kernels (from cooperative_groups_reduction.cu)
// ============================================================================

template<int BLOCK_SIZE>
__global__ void reduction_cg_thread_block(const float* __restrict__ input,
                                           float* __restrict__ output,
                                           int n);

template<int BLOCK_SIZE>
__global__ void reduction_cg_tiled(const float* __restrict__ input,
                                    float* __restrict__ output,
                                    int n);

template<int BLOCK_SIZE>
__global__ void reduction_cg_coalesced(const float* __restrict__ input,
                                        float* __restrict__ output,
                                        int n,
                                        int threshold);

template<int BLOCK_SIZE>
__global__ void reduction_cg_grid(float* __restrict__ data,
                                   float* __restrict__ temp,
                                   int n);

template<int BLOCK_SIZE>
__global__ void reduction_cg_segmented(const float* __restrict__ input,
                                        float* __restrict__ output,
                                        const int* __restrict__ segment_ids,
                                        const int* __restrict__ segment_offsets,
                                        int num_segments,
                                        int n);

template<int BLOCK_SIZE, int TILE_SIZE>
__global__ void reduction_cg_hierarchical(const float* __restrict__ input,
                                           float* __restrict__ output,
                                           int n);

// Host utility functions
bool supports_cooperative_launch(int device = 0);

int get_max_cooperative_blocks(int device, void* kernel, int block_size, int dynamic_smem = 0);

// ============================================================================
// Advanced Pattern Kernels (from cooperative_groups_patterns.cu)
// ============================================================================

template<int BLOCK_SIZE>
__global__ void bitonic_sort_cg(int* data, int n);

template<int BLOCK_SIZE, int NUM_BINS>
__global__ void histogram_cg_warp_aggregated(const int* __restrict__ data,
                                               int* __restrict__ histogram,
                                               int n);

template<int BLOCK_SIZE>
__global__ void histogram_cg_labeled(const int* __restrict__ data,
                                      int* __restrict__ histogram,
                                      int n,
                                      int num_bins);

template<int TILE_SIZE>
__global__ void matrix_transpose_cg(const float* __restrict__ input,
                                     float* __restrict__ output,
                                     int width,
                                     int height);

template<int TILE_SIZE>
__global__ void matrix_multiply_cg(const float* __restrict__ A,
                                    const float* __restrict__ B,
                                    float* __restrict__ C,
                                    int M, int N, int K);

template<int BLOCK_SIZE>
__global__ void scan_cg_inclusive(const float* __restrict__ input,
                                   float* __restrict__ output,
                                   float* __restrict__ block_aggregates,
                                   int n);

template<int BLOCK_SIZE>
__global__ void scan_cg_exclusive(const float* __restrict__ input,
                                   float* __restrict__ output,
                                   int n);

template<int BLOCK_SIZE>
__global__ void dot_product_cg(const float* __restrict__ a,
                                const float* __restrict__ b,
                                float* __restrict__ result,
                                int n);
