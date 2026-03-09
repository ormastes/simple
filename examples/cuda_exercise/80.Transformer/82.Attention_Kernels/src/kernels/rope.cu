/**
 * @file rope.cu
 * @brief Rotary Position Embeddings (RoPE)
 *
 * Implements in-place rotary position embeddings as described in the RoFormer paper.
 * RoPE encodes absolute position by rotating pairs of dimensions using position-dependent
 * frequencies, which enables the dot product between query and key to depend only on
 * their relative position.
 */
#include <cuda_runtime.h>
#include <cmath>

namespace transformer {

/**
 * @brief RoPE kernel: apply rotary position embeddings in-place
 *
 * For each pair of dimensions (d, d + half_dim), computes:
 *   x'[d]            = x[d] * cos(theta) - x[d + half_dim] * sin(theta)
 *   x'[d + half_dim] = x[d] * sin(theta) + x[d + half_dim] * cos(theta)
 * where theta = position * (1 / theta_base^(2d/head_dim))
 *
 * @param[in,out] x         Tensor with layout [batch, seq_len, num_heads, head_dim]
 * @param[in]     seq_len   Sequence length
 * @param[in]     num_heads Number of attention heads
 * @param[in]     head_dim  Dimension per head (must be even)
 * @param[in]     theta_base Base frequency for rotation (typically 10000.0)
 */
__global__ void rope_kernel(float* __restrict__ x, int seq_len, int num_heads,
                            int head_dim, float theta_base) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    int half_dim = head_dim / 2;
    int total_elements = gridDim.x * blockDim.x;

    // Each thread handles one (batch, position, head, dimension_pair)
    // Decode flat index into multi-dimensional indices
    int d = idx % half_dim;
    int remaining = idx / half_dim;
    int h = remaining % num_heads;
    int t = (remaining / num_heads) % seq_len;
    int b = remaining / (num_heads * seq_len);

    // Bounds check: total valid elements = batch * seq_len * num_heads * half_dim
    // We rely on grid sizing, but guard with batch check
    if (remaining / (num_heads * seq_len) != b) return;

    // Compute rotation angle for this position and dimension pair
    float freq = 1.0f / powf(theta_base, (2.0f * d) / head_dim);
    float angle = t * freq;
    float cos_val = cosf(angle);
    float sin_val = sinf(angle);

    // Compute base index into the flattened tensor
    int base_idx = b * (seq_len * num_heads * head_dim) +
                   t * (num_heads * head_dim) +
                   h * head_dim;

    float x0 = x[base_idx + d];
    float x1 = x[base_idx + d + half_dim];

    x[base_idx + d]            = x0 * cos_val - x1 * sin_val;
    x[base_idx + d + half_dim] = x0 * sin_val + x1 * cos_val;
}

/**
 * @brief Launch RoPE kernel
 *
 * @param[in,out] x         Tensor [batch, seq_len, num_heads, head_dim]
 * @param[in]     batch     Batch size
 * @param[in]     seq_len   Sequence length
 * @param[in]     num_heads Number of attention heads
 * @param[in]     head_dim  Dimension per head (must be even)
 * @param[in]     theta_base Base frequency (default 10000.0)
 * @param[in]     stream    CUDA stream
 */
void launch_rope(float* x, int batch, int seq_len, int num_heads, int head_dim,
                 float theta_base, cudaStream_t stream) {
    int half_dim = head_dim / 2;
    int total = batch * seq_len * num_heads * half_dim;
    int block = 256;
    int grid = (total + block - 1) / block;
    rope_kernel<<<grid, block, 0, stream>>>(x, seq_len, num_heads, head_dim, theta_base);
}

} // namespace transformer
