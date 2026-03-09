/**
 * @file rmsnorm.cu
 * @brief RMSNorm kernel implementation using Module 88 reduction primitives
 *
 * Implements Root Mean Square Layer Normalization:
 *   output[i] = weight[i] * input[i] * rsqrt(mean(input^2) + eps)
 *
 * Uses compute_rms_rsqrt from Module 88 (Normalization_Common_API) for the
 * block-level reduction that computes rsqrt(mean(x^2) + eps).
 */
#include "common/rmsnorm.cuh"
#include "common/mean_rsqrt.cuh"  // from 88_Normalization_Common_API
#include <cuda_runtime.h>
#include <cuda_fp16.h>

namespace transformer {

/**
 * @brief RMSNorm kernel -- one block per row
 *
 * Phase 1: Each thread accumulates squared values in a stride loop, then
 *          block_reduce_sum produces the sum of squares. The rsqrt scaling
 *          factor is computed from mean(x^2) + eps.
 *
 * Phase 2: Each thread scales its assigned elements by weight * rsqrt_factor.
 *
 * @param[out] output Normalized output [batch_size, hidden_dim]
 * @param[in] input Input tensor [batch_size, hidden_dim]
 * @param[in] weight Scale parameter [hidden_dim]
 * @param[in] hidden_dim Feature dimension
 * @param[in] eps Numerical stability epsilon
 */
__global__ void rmsnorm_kernel(float* __restrict__ output,
                                const float* __restrict__ input,
                                const float* __restrict__ weight,
                                int hidden_dim, float eps) {
    // Shared memory for block reduction
    extern __shared__ float smem[];

    int row = blockIdx.x;
    const float* row_input = input + row * hidden_dim;
    float* row_output = output + row * hidden_dim;

    // Compute rsqrt(mean(x^2) + eps) using Module 88 primitive
    float rms_scale = compute_rms_rsqrt(row_input, hidden_dim, eps, smem);

    // Apply normalization: output[i] = weight[i] * input[i] * rms_scale
    for (int i = threadIdx.x; i < hidden_dim; i += blockDim.x) {
        row_output[i] = weight[i] * row_input[i] * rms_scale;
    }
}

/**
 * @brief fp16 RMSNorm kernel -- internal computation in fp32
 *
 * Loads fp16 values, converts to fp32 for the reduction, then stores the
 * normalized result back as fp16.
 */
__global__ void rmsnorm_fp16_kernel(half* __restrict__ output,
                                     const half* __restrict__ input,
                                     const half* __restrict__ weight,
                                     int hidden_dim, float eps) {
    extern __shared__ float smem[];

    int row = blockIdx.x;
    const half* row_input = input + row * hidden_dim;
    half* row_output = output + row * hidden_dim;

    // Phase 1: compute sum of squares in fp32
    float sum_sq = 0.0f;
    for (int i = threadIdx.x; i < hidden_dim; i += blockDim.x) {
        float val = __half2float(row_input[i]);
        sum_sq += val * val;
    }
    sum_sq = block_reduce_sum(sum_sq, smem);
    float rms_scale = rsqrtf(sum_sq / static_cast<float>(hidden_dim) + eps);

    // Phase 2: apply normalization
    for (int i = threadIdx.x; i < hidden_dim; i += blockDim.x) {
        float val = __half2float(row_input[i]);
        float w = __half2float(weight[i]);
        row_output[i] = __float2half(w * val * rms_scale);
    }
}

// ---------------------------------------------------------------------------
// Host launch functions
// ---------------------------------------------------------------------------

void launch_rmsnorm(float* output, const float* input, const float* weight,
                    int batch_size, int hidden_dim, float eps,
                    cudaStream_t stream) {
    // Choose block size: use 256 threads for hidden_dim >= 256, otherwise align to 32
    int block_size = (hidden_dim >= 256) ? 256 : ((hidden_dim + 31) / 32) * 32;
    block_size = min(block_size, 1024);

    // Shared memory: need ceil(block_size / 32) floats for block reduction
    int smem_size = ((block_size + 31) / 32) * sizeof(float);

    rmsnorm_kernel<<<batch_size, block_size, smem_size, stream>>>(
        output, input, weight, hidden_dim, eps);
}

void launch_rmsnorm_fp16(void* output, const void* input, const void* weight,
                         int batch_size, int hidden_dim, float eps,
                         cudaStream_t stream) {
    int block_size = (hidden_dim >= 256) ? 256 : ((hidden_dim + 31) / 32) * 32;
    block_size = min(block_size, 1024);
    int smem_size = ((block_size + 31) / 32) * sizeof(float);

    rmsnorm_fp16_kernel<<<batch_size, block_size, smem_size, stream>>>(
        static_cast<half*>(output),
        static_cast<const half*>(input),
        static_cast<const half*>(weight),
        hidden_dim, eps);
}

} // namespace transformer
