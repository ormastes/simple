/**
 * @file activation.cu
 * @brief GPU activation function kernels (GELU, SiLU, SwiGLU)
 *
 * Standalone pointwise activation kernels for MLP layers. These are used
 * when the activation cannot be fused into a GEMM epilogue, for example
 * in gated architectures (LLaMA SwiGLU) where the gate and value paths
 * are computed separately before combining.
 */
#include "common/activation.cuh"
#include <cuda_runtime.h>
#include <cuda_fp16.h>

namespace transformer {

/**
 * @brief GELU activation kernel (tanh approximation)
 *
 * Implements the GELU activation using the fast tanh approximation:
 * GELU(x) = x * 0.5 * (1 + tanh(sqrt(2/pi) * (x + 0.044715 * x^3)))
 */
__global__ void gelu_kernel(float* output, const float* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        float x = input[idx];
        float cdf = 0.5f * (1.0f + tanhf(0.7978845608f * (x + 0.044715f * x * x * x)));
        output[idx] = x * cdf;
    }
}

/**
 * @brief SiLU (Swish) activation kernel
 *
 * Implements SiLU(x) = x * sigmoid(x) = x / (1 + exp(-x)).
 * Used in LLaMA and other modern architectures as the base for SwiGLU.
 */
__global__ void silu_kernel(float* output, const float* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        float x = input[idx];
        output[idx] = x / (1.0f + expf(-x));
    }
}

/**
 * @brief SwiGLU activation kernel
 *
 * Computes SwiGLU(x, gate) = gate * SiLU(x) where x and gate are the
 * first and second halves of the input tensor respectively.
 * This is the gated activation used in LLaMA FFN blocks.
 */
__global__ void swiglu_kernel(float* output, const float* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    int half_n = n / 2;
    if (idx < half_n) {
        float x = input[idx];
        float gate = input[idx + half_n];
        float silu_x = x / (1.0f + expf(-x));
        output[idx] = gate * silu_x;
    }
}

/**
 * @brief fp16 GELU activation kernel
 *
 * Same approximation as the fp32 variant but operates on half-precision
 * inputs and outputs. Internal computation is done in fp32 for accuracy.
 */
__global__ void gelu_fp16_kernel(half* output, const half* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        float x = __half2float(input[idx]);
        float cdf = 0.5f * (1.0f + tanhf(0.7978845608f * (x + 0.044715f * x * x * x)));
        output[idx] = __float2half(x * cdf);
    }
}

// ---------------------------------------------------------------------------
// Host launch functions
// ---------------------------------------------------------------------------

void launch_gelu(float* output, const float* input, int n, cudaStream_t stream) {
    int block = 256;
    int grid = (n + block - 1) / block;
    gelu_kernel<<<grid, block, 0, stream>>>(output, input, n);
}

void launch_silu(float* output, const float* input, int n, cudaStream_t stream) {
    int block = 256;
    int grid = (n + block - 1) / block;
    silu_kernel<<<grid, block, 0, stream>>>(output, input, n);
}

void launch_swiglu(float* output, const float* input, int n, cudaStream_t stream) {
    int block = 256;
    int grid = (n / 2 + block - 1) / block;
    swiglu_kernel<<<grid, block, 0, stream>>>(output, input, n);
}

void launch_gelu_fp16(half* output, const half* input, int n, cudaStream_t stream) {
    int block = 256;
    int grid = (n + block - 1) / block;
    gelu_fp16_kernel<<<grid, block, 0, stream>>>(output, input, n);
}

} // namespace transformer
