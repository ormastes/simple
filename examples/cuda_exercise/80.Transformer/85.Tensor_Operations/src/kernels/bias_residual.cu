/**
 * @file bias_residual.cu
 * @brief Fused bias + residual addition kernel
 */
#include <cuda_runtime.h>

namespace transformer {

__global__ void bias_residual_kernel(float* output, const float* input,
                                      const float* bias, const float* residual,
                                      int rows, int cols) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= rows * cols) return;
    int col = idx % cols;
    output[idx] = input[idx] + bias[col] + residual[idx];
}

void launch_bias_residual(float* output, const float* input,
                          const float* bias, const float* residual,
                          int rows, int cols, cudaStream_t stream = 0) {
    int n = rows * cols;
    int block = 256;
    int grid = (n + block - 1) / block;
    bias_residual_kernel<<<grid, block, 0, stream>>>(output, input, bias, residual, rows, cols);
}

} // namespace transformer
