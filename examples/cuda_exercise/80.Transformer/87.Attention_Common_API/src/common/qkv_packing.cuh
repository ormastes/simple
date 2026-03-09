/**
 * @file qkv_packing.cuh
 * @brief QKV tensor layout reordering utilities
 *
 * Converts between [B,T,H,D] (natural) and [B,H,T,D] (computation) layouts
 * for multi-head attention.
 */
#pragma once
#include <cuda_runtime.h>

namespace transformer {

/**
 * @brief Reorder kernel: [B,T,H,D] -> [B,H,T,D]
 *
 * Each thread handles one element. The input uses the natural layout
 * where heads are interleaved per token, and the output groups all
 * tokens for a given head together for efficient GEMM computation.
 *
 * @param[out] output Destination tensor in [B,H,T,D] layout
 * @param[in] input Source tensor in [B,T,H,D] layout
 * @param[in] B Batch size
 * @param[in] T Sequence length
 * @param[in] H Number of attention heads
 * @param[in] D Head dimension
 */
__global__ void bthd_to_bhtd(float* __restrict__ output,
                              const float* __restrict__ input,
                              int B, int T, int H, int D) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    int total = B * T * H * D;
    if (idx >= total) return;

    int d = idx % D;
    int h = (idx / D) % H;
    int t = (idx / (D * H)) % T;
    int b = idx / (D * H * T);

    int src_idx = b * (T * H * D) + t * (H * D) + h * D + d;
    int dst_idx = b * (H * T * D) + h * (T * D) + t * D + d;

    output[dst_idx] = input[src_idx];
}

/**
 * @brief Reorder kernel: [B,H,T,D] -> [B,T,H,D]
 *
 * Inverse of bthd_to_bhtd. Converts from computation layout back
 * to the natural interleaved layout.
 *
 * @param[out] output Destination tensor in [B,T,H,D] layout
 * @param[in] input Source tensor in [B,H,T,D] layout
 * @param[in] B Batch size
 * @param[in] T Sequence length
 * @param[in] H Number of attention heads
 * @param[in] D Head dimension
 */
__global__ void bhtd_to_bthd(float* __restrict__ output,
                              const float* __restrict__ input,
                              int B, int T, int H, int D) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    int total = B * T * H * D;
    if (idx >= total) return;

    int d = idx % D;
    int t = (idx / D) % T;
    int h = (idx / (D * T)) % H;
    int b = idx / (D * T * H);

    int src_idx = b * (H * T * D) + h * (T * D) + t * D + d;
    int dst_idx = b * (T * H * D) + t * (H * D) + h * D + d;

    output[dst_idx] = input[src_idx];
}

/**
 * @brief Host function to launch BTHD->BHTD reorder
 * @param[out] output Destination tensor in [B,H,T,D] layout
 * @param[in] input Source tensor in [B,T,H,D] layout
 * @param[in] B Batch size
 * @param[in] T Sequence length
 * @param[in] H Number of attention heads
 * @param[in] D Head dimension
 * @param[in] stream CUDA stream (default: 0)
 */
inline void reorder_bthd_to_bhtd(float* output, const float* input,
                                  int B, int T, int H, int D, cudaStream_t stream = 0) {
    int total = B * T * H * D;
    int block = 256;
    int grid = (total + block - 1) / block;
    bthd_to_bhtd<<<grid, block, 0, stream>>>(output, input, B, T, H, D);
}

/**
 * @brief Host function to launch BHTD->BTHD reorder
 * @param[out] output Destination tensor in [B,T,H,D] layout
 * @param[in] input Source tensor in [B,H,T,D] layout
 * @param[in] B Batch size
 * @param[in] T Sequence length
 * @param[in] H Number of attention heads
 * @param[in] D Head dimension
 * @param[in] stream CUDA stream (default: 0)
 */
inline void reorder_bhtd_to_bthd(float* output, const float* input,
                                  int B, int T, int H, int D, cudaStream_t stream = 0) {
    int total = B * T * H * D;
    int block = 256;
    int grid = (total + block - 1) / block;
    bhtd_to_bthd<<<grid, block, 0, stream>>>(output, input, B, T, H, D);
}

} // namespace transformer
