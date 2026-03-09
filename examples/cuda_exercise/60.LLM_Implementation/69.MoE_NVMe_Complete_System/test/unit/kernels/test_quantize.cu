/**
 * @file test_quantize.cu
 * @brief Unit tests for INT8 quantization/dequantization kernels
 *
 * Validates the quantize-dequantize roundtrip preserves values
 * within acceptable error bounds.
 */

#include <gtest/gtest.h>
#include <cuda_runtime.h>
#include <cmath>
#include <vector>

namespace llm {
// Forward declarations of functions from quantize_kernels.cu
void quantize_fp32_to_int8(int8_t* quantized, float* scales,
                           const float* weights,
                           int num_channels, int channel_size,
                           cudaStream_t stream);
void dequantize_int8_to_fp32(float* weights, const int8_t* quantized,
                             const float* scales,
                             int num_channels, int channel_size,
                             cudaStream_t stream);
} // namespace llm

class QuantizeKernelTest : public ::testing::Test {
protected:
    static constexpr int NUM_CHANNELS = 16;
    static constexpr int CHANNEL_SIZE = 256;
    static constexpr int TOTAL = NUM_CHANNELS * CHANNEL_SIZE;

    float* d_weights;
    float* d_reconstructed;
    float* d_scales;
    int8_t* d_quantized;

    std::vector<float> h_weights;

    void SetUp() override {
        h_weights.resize(TOTAL);

        // Initialize with a range of values including negative
        for (int c = 0; c < NUM_CHANNELS; ++c) {
            float channel_scale = (float)(c + 1) * 0.5f;
            for (int i = 0; i < CHANNEL_SIZE; ++i) {
                h_weights[c * CHANNEL_SIZE + i] =
                    channel_scale * sinf((float)i * 0.1f);
            }
        }

        cudaMalloc(&d_weights, TOTAL * sizeof(float));
        cudaMalloc(&d_reconstructed, TOTAL * sizeof(float));
        cudaMalloc(&d_scales, NUM_CHANNELS * sizeof(float));
        cudaMalloc(&d_quantized, TOTAL * sizeof(int8_t));

        cudaMemcpy(d_weights, h_weights.data(), TOTAL * sizeof(float), cudaMemcpyHostToDevice);
    }

    void TearDown() override {
        cudaFree(d_weights);
        cudaFree(d_reconstructed);
        cudaFree(d_scales);
        cudaFree(d_quantized);
    }
};

/// Test quantize-dequantize roundtrip error is bounded
TEST_F(QuantizeKernelTest, RoundtripError) {
    llm::quantize_fp32_to_int8(d_quantized, d_scales, d_weights,
                               NUM_CHANNELS, CHANNEL_SIZE, 0);
    llm::dequantize_int8_to_fp32(d_reconstructed, d_quantized, d_scales,
                                 NUM_CHANNELS, CHANNEL_SIZE, 0);
    cudaDeviceSynchronize();

    std::vector<float> h_reconstructed(TOTAL);
    cudaMemcpy(h_reconstructed.data(), d_reconstructed, TOTAL * sizeof(float), cudaMemcpyDeviceToHost);

    float max_abs_error = 0.0f;
    float max_rel_error = 0.0f;
    for (int i = 0; i < TOTAL; ++i) {
        float abs_err = fabsf(h_weights[i] - h_reconstructed[i]);
        if (abs_err > max_abs_error) max_abs_error = abs_err;

        if (fabsf(h_weights[i]) > 1e-6f) {
            float rel_err = abs_err / fabsf(h_weights[i]);
            if (rel_err > max_rel_error) max_rel_error = rel_err;
        }
    }

    // INT8 quantization should have <1% relative error for most values
    // Maximum absolute error should be bounded by scale/127
    EXPECT_LT(max_abs_error, 0.1f)
        << "Maximum absolute error too large";
}

/// Test that zero values remain zero after roundtrip
TEST_F(QuantizeKernelTest, ZeroPreservation) {
    std::vector<float> zeros(TOTAL, 0.0f);
    cudaMemcpy(d_weights, zeros.data(), TOTAL * sizeof(float), cudaMemcpyHostToDevice);

    llm::quantize_fp32_to_int8(d_quantized, d_scales, d_weights,
                               NUM_CHANNELS, CHANNEL_SIZE, 0);
    llm::dequantize_int8_to_fp32(d_reconstructed, d_quantized, d_scales,
                                 NUM_CHANNELS, CHANNEL_SIZE, 0);
    cudaDeviceSynchronize();

    std::vector<float> h_reconstructed(TOTAL);
    cudaMemcpy(h_reconstructed.data(), d_reconstructed, TOTAL * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < TOTAL; ++i) {
        EXPECT_FLOAT_EQ(h_reconstructed[i], 0.0f)
            << "Zero not preserved at index " << i;
    }
}

/// Test that per-channel scales are positive
TEST_F(QuantizeKernelTest, PositiveScales) {
    llm::quantize_fp32_to_int8(d_quantized, d_scales, d_weights,
                               NUM_CHANNELS, CHANNEL_SIZE, 0);
    cudaDeviceSynchronize();

    std::vector<float> h_scales(NUM_CHANNELS);
    cudaMemcpy(h_scales.data(), d_scales, NUM_CHANNELS * sizeof(float), cudaMemcpyDeviceToHost);

    for (int c = 0; c < NUM_CHANNELS; ++c) {
        EXPECT_GT(h_scales[c], 0.0f)
            << "Scale for channel " << c << " should be positive";
    }
}

/// Test quantization with uniform values
TEST_F(QuantizeKernelTest, UniformValues) {
    std::vector<float> uniform(TOTAL);
    for (int i = 0; i < TOTAL; ++i) {
        uniform[i] = 0.5f;
    }
    cudaMemcpy(d_weights, uniform.data(), TOTAL * sizeof(float), cudaMemcpyHostToDevice);

    llm::quantize_fp32_to_int8(d_quantized, d_scales, d_weights,
                               NUM_CHANNELS, CHANNEL_SIZE, 0);
    llm::dequantize_int8_to_fp32(d_reconstructed, d_quantized, d_scales,
                                 NUM_CHANNELS, CHANNEL_SIZE, 0);
    cudaDeviceSynchronize();

    std::vector<float> h_reconstructed(TOTAL);
    cudaMemcpy(h_reconstructed.data(), d_reconstructed, TOTAL * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < TOTAL; ++i) {
        EXPECT_NEAR(h_reconstructed[i], 0.5f, 0.01f)
            << "Uniform value not preserved at index " << i;
    }
}

/// Test that quantized values are within INT8 range
TEST_F(QuantizeKernelTest, Int8Range) {
    llm::quantize_fp32_to_int8(d_quantized, d_scales, d_weights,
                               NUM_CHANNELS, CHANNEL_SIZE, 0);
    cudaDeviceSynchronize();

    std::vector<int8_t> h_quantized(TOTAL);
    cudaMemcpy(h_quantized.data(), d_quantized, TOTAL * sizeof(int8_t), cudaMemcpyDeviceToHost);

    for (int i = 0; i < TOTAL; ++i) {
        EXPECT_GE((int)h_quantized[i], -127);
        EXPECT_LE((int)h_quantized[i], 127);
    }
}
