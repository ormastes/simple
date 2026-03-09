/**
 * @file rms_norm.cu
 * @brief CUDA kernel implementation for RMS Normalization
 *
 * Implements RMS Normalization using shared memory reduction to compute
 * the root mean square of each row. Each thread block processes one row.
 */

#include "common/rms_norm.h"
#include "cuda_utils.h"
#include <vector>

namespace llm {

/**
 * @brief RMS Normalization kernel
 *
 * Algorithm:
 * 1. Each thread accumulates partial sum of squares for its elements
 * 2. Shared memory reduction computes the total sum of squares
 * 3. Compute RMS: rsqrt(mean(x^2) + eps)
 * 4. Each thread normalizes its elements: weight * x * rms_inv
 */
__global__ void rms_norm_kernel(float* output, const float* input,
                                const float* weight,
                                int hidden_dim, float eps) {
    // Each block handles one row
    int row = blockIdx.x;
    int tid = threadIdx.x;
    int block_size = blockDim.x;

    const float* row_input = input + row * hidden_dim;
    float* row_output = output + row * hidden_dim;

    // Shared memory for reduction
    extern __shared__ float shared[];

    // Step 1: Compute partial sum of squares
    float local_sum_sq = 0.0f;
    for (int i = tid; i < hidden_dim; i += block_size) {
        float val = row_input[i];
        local_sum_sq += val * val;
    }
    shared[tid] = local_sum_sq;
    __syncthreads();

    // Reduction for sum of squares
    for (int stride = block_size / 2; stride > 0; stride >>= 1) {
        if (tid < stride) {
            shared[tid] += shared[tid + stride];
        }
        __syncthreads();
    }

    // Step 2: Compute inverse RMS
    float rms_inv = rsqrtf(shared[0] / hidden_dim + eps);
    __syncthreads();

    // Step 3: Normalize and apply weight
    for (int i = tid; i < hidden_dim; i += block_size) {
        row_output[i] = weight[i] * row_input[i] * rms_inv;
    }
}

void rms_norm_forward(float* output, const float* input, const float* weight,
                     int batch_size, int hidden_dim, float eps,
                     cudaStream_t stream) {
    int block_size = (hidden_dim < 1024) ? hidden_dim : 1024;
    // Round up to next power of 2 for efficient reduction
    int rounded = 1;
    while (rounded < block_size) rounded <<= 1;
    if (rounded > 1024) rounded = 1024;
    block_size = rounded;

    dim3 grid(batch_size);
    dim3 block(block_size);
    size_t shared_mem = block_size * sizeof(float);

    rms_norm_kernel<<<grid, block, shared_mem, stream>>>(
        output, input, weight, hidden_dim, eps);
    CHECK_CUDA(cudaGetLastError());
}

float* allocate_rms_norm_weights(int hidden_dim) {
    float* weight = cuda_malloc<float>(hidden_dim);

    // Initialize weight = 1.0
    std::vector<float> h_weight(hidden_dim, 1.0f);
    CHECK_CUDA(cudaMemcpy(weight, h_weight.data(),
                          hidden_dim * sizeof(float), cudaMemcpyHostToDevice));
    return weight;
}

void free_rms_norm_weights(float*& weight) {
    cuda_free(weight);
    weight = nullptr;
}

} // namespace llm
