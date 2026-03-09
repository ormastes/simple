/**
 * @file softmax.cu
 * @brief Standalone numerically stable softmax kernel
 *
 * Implements a parallelized row-wise softmax using warp-level shuffle reductions
 * for finding the row maximum and computing the normalization sum. This is the
 * standalone version used outside of fused attention kernels.
 */
#include <cuda_runtime.h>
#include <cfloat>

namespace transformer {

/**
 * @brief Row-wise softmax kernel
 *
 * Each block processes one row of the input matrix. The algorithm proceeds in
 * three phases: (1) find the row maximum via warp shuffle reduction, (2) compute
 * exp(x - max) and accumulate the sum, (3) normalize by dividing by the sum.
 *
 * @param[out] output Output matrix with softmax probabilities
 * @param[in]  input  Input matrix of raw logits
 * @param[in]  rows   Number of rows
 * @param[in]  cols   Number of columns per row
 */
__global__ void softmax_kernel(float* output, const float* input, int rows, int cols) {
    extern __shared__ float smem[];

    int row = blockIdx.x;
    if (row >= rows) return;

    const float* row_in = input + row * cols;
    float* row_out = output + row * cols;

    // Phase 1: Find max value in the row
    float max_val = -FLT_MAX;
    for (int i = threadIdx.x; i < cols; i += blockDim.x) {
        max_val = fmaxf(max_val, row_in[i]);
    }

    // Warp reduce max
    for (int offset = 16; offset > 0; offset >>= 1) {
        max_val = fmaxf(max_val, __shfl_xor_sync(0xffffffff, max_val, offset));
    }

    int lane = threadIdx.x % 32;
    int warp_id = threadIdx.x / 32;
    if (lane == 0) smem[warp_id] = max_val;
    __syncthreads();

    if (warp_id == 0) {
        int num_warps = (blockDim.x + 31) / 32;
        max_val = (lane < num_warps) ? smem[lane] : -FLT_MAX;
        for (int offset = 16; offset > 0; offset >>= 1) {
            max_val = fmaxf(max_val, __shfl_xor_sync(0xffffffff, max_val, offset));
        }
        if (lane == 0) smem[0] = max_val;
    }
    __syncthreads();
    max_val = smem[0];

    // Phase 2: Compute exp(x - max) and accumulate sum
    float sum = 0.0f;
    for (int i = threadIdx.x; i < cols; i += blockDim.x) {
        float val = expf(row_in[i] - max_val);
        row_out[i] = val;
        sum += val;
    }

    // Reduce sum across warps
    for (int offset = 16; offset > 0; offset >>= 1) {
        sum += __shfl_xor_sync(0xffffffff, sum, offset);
    }
    if (lane == 0) smem[warp_id] = sum;
    __syncthreads();

    if (warp_id == 0) {
        int num_warps = (blockDim.x + 31) / 32;
        sum = (lane < num_warps) ? smem[lane] : 0.0f;
        for (int offset = 16; offset > 0; offset >>= 1) {
            sum += __shfl_xor_sync(0xffffffff, sum, offset);
        }
        if (lane == 0) smem[0] = sum;
    }
    __syncthreads();
    float inv_sum = 1.0f / smem[0];

    // Phase 3: Normalize
    for (int i = threadIdx.x; i < cols; i += blockDim.x) {
        row_out[i] *= inv_sum;
    }
}

/**
 * @brief Launch row-wise softmax kernel
 *
 * @param[out] output Output matrix [rows x cols]
 * @param[in]  input  Input matrix [rows x cols]
 * @param[in]  rows   Number of rows
 * @param[in]  cols   Number of columns
 * @param[in]  stream CUDA stream for asynchronous execution
 */
void launch_softmax(float* output, const float* input, int rows, int cols,
                    cudaStream_t stream) {
    int block = min(256, ((cols + 31) / 32) * 32);
    if (block < 32) block = 32;
    int smem = (block / 32) * sizeof(float);
    softmax_kernel<<<rows, block, smem, stream>>>(output, input, rows, cols);
}

} // namespace transformer
