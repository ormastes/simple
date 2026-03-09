/**
 * @file gradient_kernels.cu
 * @brief CUDA kernels for gradient manipulation utilities
 *
 * Provides GPU kernels for gradient clipping (by global norm) and
 * gradient accumulation. Gradient clipping prevents exploding gradients
 * during LLM training, while gradient accumulation enables larger
 * effective batch sizes on memory-constrained hardware.
 */

#include <cuda_runtime.h>
#include <cmath>

namespace llm {

/**
 * @brief Compute squared L2 norm of a vector (reduction kernel)
 *
 * Each block computes a partial sum of squared elements. The final
 * reduction must be completed on the host or with a second kernel.
 *
 * @param[in]  data          Input vector [n]
 * @param[out] partial_sums  Partial squared norms [gridDim.x]
 * @param[in]  n             Vector length
 */
__global__ void squared_norm_kernel(
    const float* data,
    float* partial_sums,
    int n
) {
    extern __shared__ float shared[];

    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Each thread accumulates its elements
    float local_sum = 0.0f;
    for (int i = idx; i < n; i += blockDim.x * gridDim.x) {
        float val = data[i];
        local_sum += val * val;
    }
    shared[threadIdx.x] = local_sum;
    __syncthreads();

    // Block-level reduction
    for (int stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (threadIdx.x < stride) {
            shared[threadIdx.x] += shared[threadIdx.x + stride];
        }
        __syncthreads();
    }

    // Write block partial sum
    if (threadIdx.x == 0) {
        partial_sums[blockIdx.x] = shared[0];
    }
}

/**
 * @brief Scale gradient elements by a constant factor
 *
 * Used after norm computation to clip: grad *= (max_norm / actual_norm)
 *
 * @param[in,out] grads  Gradient vector [n]
 * @param[in]     scale  Scaling factor
 * @param[in]     n      Vector length
 */
__global__ void scale_kernel(
    float* grads,
    float scale,
    int n
) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        grads[idx] *= scale;
    }
}

/**
 * @brief Clip gradients by global L2 norm
 *
 * If the global L2 norm of the gradient vector exceeds max_norm,
 * all elements are scaled down proportionally so the norm equals max_norm.
 * If the norm is already within bounds, gradients are left unchanged.
 *
 * Algorithm:
 *   norm = sqrt(sum(grad[i]^2))
 *   if norm > max_norm:
 *     grad *= max_norm / norm
 *
 * @param[in,out] d_grads   Gradient vector (device) [num_params]
 * @param[in]     num_params Number of gradient elements
 * @param[in]     max_norm   Maximum allowed gradient norm
 * @param[in]     stream     CUDA stream (default: 0)
 *
 * @return The original gradient norm (before clipping)
 */
float gradient_clip_by_norm(float* d_grads, int num_params, float max_norm,
                            cudaStream_t stream = 0) {
    int block_size = 256;
    int grid_size = (num_params + block_size - 1) / block_size;
    grid_size = (grid_size > 1024) ? 1024 : grid_size;  // Cap grid size

    // Allocate partial sums buffer
    float* d_partial_sums = nullptr;
    cudaMalloc(&d_partial_sums, grid_size * sizeof(float));

    // Step 1: Compute squared norm (partial sums)
    int shared_mem = block_size * sizeof(float);
    squared_norm_kernel<<<grid_size, block_size, shared_mem, stream>>>(
        d_grads, d_partial_sums, num_params
    );

    // Step 2: Copy partial sums to host and reduce
    float* h_partial_sums = new float[grid_size];
    cudaMemcpy(h_partial_sums, d_partial_sums, grid_size * sizeof(float),
               cudaMemcpyDeviceToHost);

    float squared_norm = 0.0f;
    for (int i = 0; i < grid_size; i++) {
        squared_norm += h_partial_sums[i];
    }
    float grad_norm = std::sqrt(squared_norm);

    // Step 3: Scale gradients if norm exceeds max_norm
    if (grad_norm > max_norm) {
        float scale = max_norm / grad_norm;
        int scale_grid = (num_params + block_size - 1) / block_size;
        scale_kernel<<<scale_grid, block_size, 0, stream>>>(
            d_grads, scale, num_params
        );
    }

    // Cleanup
    delete[] h_partial_sums;
    cudaFree(d_partial_sums);

    return grad_norm;
}

/**
 * @brief Accumulate gradients kernel
 *
 * Adds source gradients to an accumulator buffer element-wise.
 * Used for gradient accumulation across micro-batches:
 *   accum[i] += grad[i]
 *
 * @param[in,out] accum  Gradient accumulator [n]
 * @param[in]     grads  Source gradients to add [n]
 * @param[in]     n      Number of elements
 */
__global__ void gradient_accumulate_kernel(
    float* accum,
    const float* grads,
    int n
) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        accum[idx] += grads[idx];
    }
}

/**
 * @brief Accumulate gradients from a micro-batch into an accumulator
 *
 * Adds source gradient values element-wise into the accumulator buffer.
 * Call this once per micro-batch, then use the accumulated gradients
 * for a single optimizer step (effectively increasing batch size).
 *
 * @param[in,out] d_accum     Gradient accumulator (device) [num_params]
 * @param[in]     d_grads     Micro-batch gradients (device) [num_params]
 * @param[in]     num_params  Number of gradient elements
 * @param[in]     stream      CUDA stream (default: 0)
 */
void gradient_accumulate(float* d_accum, const float* d_grads,
                         int num_params, cudaStream_t stream = 0) {
    int block_size = 256;
    int grid_size = (num_params + block_size - 1) / block_size;
    gradient_accumulate_kernel<<<grid_size, block_size, 0, stream>>>(
        d_accum, d_grads, num_params
    );
}

/**
 * @brief Zero out a gradient buffer
 *
 * Resets gradient accumulator to zero before starting a new accumulation
 * window.
 *
 * @param[out] d_grads     Gradient buffer (device) [num_params]
 * @param[in]  num_params  Number of elements
 * @param[in]  stream      CUDA stream (default: 0)
 */
void gradient_zero(float* d_grads, int num_params, cudaStream_t stream = 0) {
    cudaMemsetAsync(d_grads, 0, num_params * sizeof(float), stream);
}

} // namespace llm
