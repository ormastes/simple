/**
 * @file quantize_kernels.cu
 * @brief Expert weight quantization and dequantization kernels
 *
 * Implements per-channel INT8 quantization for expert weight tensors
 * to reduce NVMe transfer sizes and GPU memory footprint. Achieves
 * approximately 4x compression with minimal accuracy loss for MoE
 * expert weights.
 */

#include <cuda_runtime.h>
#include <cfloat>
#include <cstdio>

namespace llm {

/**
 * @brief Kernel: find per-channel absolute maximum for quantization scale
 *
 * Each block handles one channel (row). Computes max(|weight|) per row
 * to determine the quantization scale factor.
 *
 * @param[out] scales   Per-channel scale factors [num_channels]
 * @param[in]  weights  FP32 weight matrix [num_channels x channel_size]
 * @param[in]  channel_size  Number of elements per channel
 */
__global__ void find_absmax_kernel(float* scales, const float* weights,
                                   int channel_size) {
    extern __shared__ float sdata[];

    int channel = blockIdx.x;
    int tid = threadIdx.x;
    int block_size = blockDim.x;

    const float* row = weights + channel * channel_size;

    float local_max = 0.0f;
    for (int i = tid; i < channel_size; i += block_size) {
        float val = fabsf(row[i]);
        if (val > local_max) local_max = val;
    }

    sdata[tid] = local_max;
    __syncthreads();

    // Reduction for max
    for (int s = block_size / 2; s > 0; s >>= 1) {
        if (tid < s) {
            if (sdata[tid + s] > sdata[tid]) {
                sdata[tid] = sdata[tid + s];
            }
        }
        __syncthreads();
    }

    if (tid == 0) {
        float absmax = sdata[0];
        scales[channel] = (absmax > 0.0f) ? (absmax / 127.0f) : 1.0f;
    }
}

/**
 * @brief Kernel: quantize FP32 weights to INT8 using per-channel scales
 *
 * @param[out] output        Quantized INT8 values [num_channels x channel_size]
 * @param[in]  input         FP32 weights [num_channels x channel_size]
 * @param[in]  scales        Per-channel scale factors [num_channels]
 * @param[in]  channel_size  Number of elements per channel
 */
__global__ void quantize_kernel(int8_t* output, const float* input,
                                const float* scales, int channel_size) {
    int channel = blockIdx.x;
    int tid = threadIdx.x;
    int block_size = blockDim.x;

    float scale = scales[channel];
    float inv_scale = 1.0f / scale;

    const float* in_row = input + channel * channel_size;
    int8_t* out_row = output + channel * channel_size;

    for (int i = tid; i < channel_size; i += block_size) {
        float val = in_row[i] * inv_scale;
        // Clamp to INT8 range
        val = fminf(fmaxf(val, -127.0f), 127.0f);
        out_row[i] = static_cast<int8_t>(roundf(val));
    }
}

/**
 * @brief Kernel: dequantize INT8 weights back to FP32
 *
 * @param[out] output        Dequantized FP32 values [num_channels x channel_size]
 * @param[in]  input         Quantized INT8 values [num_channels x channel_size]
 * @param[in]  scales        Per-channel scale factors [num_channels]
 * @param[in]  channel_size  Number of elements per channel
 */
__global__ void dequantize_kernel(float* output, const int8_t* input,
                                  const float* scales, int channel_size) {
    int channel = blockIdx.x;
    int tid = threadIdx.x;
    int block_size = blockDim.x;

    float scale = scales[channel];

    const int8_t* in_row = input + channel * channel_size;
    float* out_row = output + channel * channel_size;

    for (int i = tid; i < channel_size; i += block_size) {
        out_row[i] = static_cast<float>(in_row[i]) * scale;
    }
}

/**
 * @brief Quantize FP32 weights to INT8 with per-channel scaling
 *
 * Performs two passes: first computes per-channel absolute maximum values
 * to determine scale factors, then quantizes each element.
 *
 * @param[out] quantized     Output INT8 buffer [num_channels x channel_size]
 * @param[out] scales        Output per-channel scale factors [num_channels]
 * @param[in]  weights       Input FP32 weights [num_channels x channel_size]
 * @param[in]  num_channels  Number of channels (rows)
 * @param[in]  channel_size  Elements per channel (columns)
 * @param[in]  stream        CUDA stream
 */
void quantize_fp32_to_int8(int8_t* quantized, float* scales,
                           const float* weights,
                           int num_channels, int channel_size,
                           cudaStream_t stream) {
    int threads = 256;
    size_t shared_size = threads * sizeof(float);

    // Pass 1: find per-channel absolute max
    find_absmax_kernel<<<num_channels, threads, shared_size, stream>>>(
        scales, weights, channel_size);

    // Pass 2: quantize
    quantize_kernel<<<num_channels, threads, 0, stream>>>(
        quantized, weights, scales, channel_size);
}

/**
 * @brief Dequantize INT8 weights back to FP32
 *
 * @param[out] weights       Output FP32 weights [num_channels x channel_size]
 * @param[in]  quantized     Input INT8 values [num_channels x channel_size]
 * @param[in]  scales        Per-channel scale factors [num_channels]
 * @param[in]  num_channels  Number of channels (rows)
 * @param[in]  channel_size  Elements per channel (columns)
 * @param[in]  stream        CUDA stream
 */
void dequantize_int8_to_fp32(float* weights, const int8_t* quantized,
                             const float* scales,
                             int num_channels, int channel_size,
                             cudaStream_t stream) {
    int threads = 256;
    dequantize_kernel<<<num_channels, threads, 0, stream>>>(
        weights, quantized, scales, channel_size);
}

} // namespace llm
