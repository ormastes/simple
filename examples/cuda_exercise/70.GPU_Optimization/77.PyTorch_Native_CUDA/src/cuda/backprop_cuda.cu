/**
 * @file backprop_cuda.cu
 * @brief Fused linear layer forward and backward CUDA kernels
 *
 * Provides native_linear_forward() and native_linear_backward() which compute
 * the linear layer operations entirely on GPU. The backward pass fuses the
 * computation of grad_input, grad_weight, and grad_bias into a single call
 * to minimise kernel launch overhead and intermediate memory traffic.
 */

#include "native_ops.h"
#include <cuda_runtime.h>

/// Tile dimension (must match matmul_cuda.cu for consistency)
constexpr int BP_TILE = 32;

/**
 * @brief Tiled matmul kernel (duplicated locally to avoid cross-TU device symbol issues)
 */
__global__ void bp_matmul_kernel(float* __restrict__ C,
                                 const float* __restrict__ A,
                                 const float* __restrict__ B,
                                 int M, int N, int K) {
    __shared__ float sA[BP_TILE][BP_TILE];
    __shared__ float sB[BP_TILE][BP_TILE];

    int row = blockIdx.y * BP_TILE + threadIdx.y;
    int col = blockIdx.x * BP_TILE + threadIdx.x;
    float acc = 0.0f;

    for (int t = 0; t < (K + BP_TILE - 1) / BP_TILE; ++t) {
        int aCol = t * BP_TILE + threadIdx.x;
        int bRow = t * BP_TILE + threadIdx.y;

        sA[threadIdx.y][threadIdx.x] = (row < M && aCol < K) ? A[row * K + aCol] : 0.0f;
        sB[threadIdx.y][threadIdx.x] = (bRow < K && col < N) ? B[bRow * N + col] : 0.0f;
        __syncthreads();

        #pragma unroll
        for (int i = 0; i < BP_TILE; ++i) acc += sA[threadIdx.y][i] * sB[i][threadIdx.x];
        __syncthreads();
    }

    if (row < M && col < N) C[row * N + col] = acc;
}

/**
 * @brief Add bias to each row: out[i][j] += bias[j]
 */
__global__ void bp_add_bias_kernel(float* __restrict__ output,
                                   const float* __restrict__ bias,
                                   int rows, int cols) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < rows * cols) {
        output[idx] += bias[idx % cols];
    }
}

/**
 * @brief Transpose kernel: out[c*rows+r] = in[r*cols+c]
 */
__global__ void bp_transpose_kernel(float* __restrict__ out,
                                    const float* __restrict__ in,
                                    int rows, int cols) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < rows * cols) {
        int r = idx / cols;
        int c = idx % cols;
        out[c * rows + r] = in[r * cols + c];
    }
}

/**
 * @brief Column-sum reduction: out[j] = sum_i in[i*cols+j]
 */
__global__ void bp_reduce_rows_kernel(float* __restrict__ output,
                                      const float* __restrict__ input,
                                      int rows, int cols) {
    int col = blockIdx.x * blockDim.x + threadIdx.x;
    if (col >= cols) return;
    float sum = 0.0f;
    for (int i = 0; i < rows; ++i) sum += input[i * cols + col];
    output[col] = sum;
}

// ---- Helper launch wrappers ----

static void launch_bp_matmul(float* C, const float* A, const float* B,
                              int M, int N, int K, cudaStream_t stream) {
    dim3 block(BP_TILE, BP_TILE);
    dim3 grid((N + BP_TILE - 1) / BP_TILE, (M + BP_TILE - 1) / BP_TILE);
    bp_matmul_kernel<<<grid, block, 0, stream>>>(C, A, B, M, N, K);
}

static void launch_bp_transpose(float* out, const float* in, int rows, int cols,
                                 cudaStream_t stream) {
    int n = rows * cols;
    int threads = 256;
    bp_transpose_kernel<<<(n + threads - 1) / threads, threads, 0, stream>>>(
            out, in, rows, cols);
}

// ---- Public API ----

void native_linear_forward(float* output, const float* input, const float* weight,
                            const float* bias, int batch, int in_f, int out_f,
                            cudaStream_t stream) {
    // Need weight^T [in_f x out_f]
    float* weight_t = nullptr;
    cudaMalloc(&weight_t, sizeof(float) * in_f * out_f);
    launch_bp_transpose(weight_t, weight, out_f, in_f, stream);

    // output[batch x out_f] = input[batch x in_f] * weight_t[in_f x out_f]
    launch_bp_matmul(output, input, weight_t, batch, out_f, in_f, stream);
    cudaFree(weight_t);

    // Add bias if provided
    if (bias) {
        int total = batch * out_f;
        int threads = 256;
        bp_add_bias_kernel<<<(total + threads - 1) / threads, threads, 0, stream>>>(
                output, bias, batch, out_f);
    }
}

void native_linear_backward(float* grad_input, float* grad_weight, float* grad_bias,
                             const float* grad_output, const float* input,
                             const float* weight,
                             int batch, int in_features, int out_features,
                             cudaStream_t stream) {
    // grad_input[batch x in] = grad_output[batch x out] * weight[out x in]
    launch_bp_matmul(grad_input, grad_output, weight, batch, in_features, out_features, stream);

    // grad_weight[out x in] = grad_output^T[out x batch] * input[batch x in]
    float* grad_out_t = nullptr;
    cudaMalloc(&grad_out_t, sizeof(float) * batch * out_features);
    launch_bp_transpose(grad_out_t, grad_output, batch, out_features, stream);
    launch_bp_matmul(grad_weight, grad_out_t, input, out_features, in_features, batch, stream);
    cudaFree(grad_out_t);

    // grad_bias[out] = sum over batch of grad_output
    if (grad_bias) {
        int threads = 256;
        bp_reduce_rows_kernel<<<(out_features + threads - 1) / threads, threads, 0, stream>>>(
                grad_bias, grad_output, batch, out_features);
    }
}
