/**
 * @file test_softmax.cu
 * @brief Unit tests for the standalone softmax kernel
 *
 * Validates row-wise softmax correctness, numerical stability with extreme values,
 * and proper probability normalization (rows sum to 1.0).
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include <vector>
#include <cmath>
#include <cfloat>
#include <algorithm>
#include <numeric>

namespace transformer {
extern void launch_softmax(float* output, const float* input, int rows, int cols,
                           cudaStream_t stream);
}

/**
 * @brief Test fixture for softmax kernel tests
 */
class SoftmaxKernelTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }

    /// CPU reference softmax for a single row
    void cpu_softmax_row(const float* input, float* output, int cols) {
        float max_val = *std::max_element(input, input + cols);
        float sum = 0.0f;
        for (int i = 0; i < cols; i++) {
            output[i] = std::exp(input[i] - max_val);
            sum += output[i];
        }
        for (int i = 0; i < cols; i++) {
            output[i] /= sum;
        }
    }
};

/**
 * @brief Verify softmax output sums to 1.0 for each row
 */
TEST_F(SoftmaxKernelTest, RowSumsToOne) {
    const int rows = 4;
    const int cols = 64;
    const int total = rows * cols;

    std::vector<float> h_input(total);
    for (int i = 0; i < total; i++) {
        h_input[i] = static_cast<float>(i % 17) * 0.3f - 2.5f;
    }

    float* d_input = cuda_malloc<float>(total);
    float* d_output = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    transformer::launch_softmax(d_output, d_input, rows, cols, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total * sizeof(float), cudaMemcpyDeviceToHost));

    for (int r = 0; r < rows; r++) {
        float sum = 0.0f;
        for (int c = 0; c < cols; c++) {
            sum += h_output[r * cols + c];
            EXPECT_GE(h_output[r * cols + c], 0.0f)
                << "Negative probability at row=" << r << ", col=" << c;
        }
        EXPECT_NEAR(sum, 1.0f, 1e-4f)
            << "Row " << r << " does not sum to 1.0";
    }

    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Verify softmax matches CPU reference implementation
 */
TEST_F(SoftmaxKernelTest, MatchesCPUReference) {
    const int rows = 8;
    const int cols = 128;
    const int total = rows * cols;

    std::vector<float> h_input(total);
    for (int i = 0; i < total; i++) {
        h_input[i] = std::sin(static_cast<float>(i) * 0.1f) * 5.0f;
    }

    float* d_input = cuda_malloc<float>(total);
    float* d_output = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    transformer::launch_softmax(d_output, d_input, rows, cols, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total * sizeof(float), cudaMemcpyDeviceToHost));

    // Compare against CPU reference
    std::vector<float> expected(cols);
    for (int r = 0; r < rows; r++) {
        cpu_softmax_row(h_input.data() + r * cols, expected.data(), cols);
        for (int c = 0; c < cols; c++) {
            EXPECT_NEAR(h_output[r * cols + c], expected[c], 1e-5f)
                << "Mismatch at row=" << r << ", col=" << c;
        }
    }

    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Numerical stability: large positive values should not produce NaN or Inf
 */
TEST_F(SoftmaxKernelTest, NumericalStability_LargeValues) {
    const int rows = 2;
    const int cols = 32;
    const int total = rows * cols;

    std::vector<float> h_input(total);
    for (int i = 0; i < total; i++) {
        h_input[i] = 500.0f + static_cast<float>(i) * 10.0f;
    }

    float* d_input = cuda_malloc<float>(total);
    float* d_output = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    transformer::launch_softmax(d_output, d_input, rows, cols, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total * sizeof(float), cudaMemcpyDeviceToHost));

    for (int i = 0; i < total; i++) {
        EXPECT_FALSE(std::isnan(h_output[i])) << "NaN at index " << i;
        EXPECT_FALSE(std::isinf(h_output[i])) << "Inf at index " << i;
        EXPECT_GE(h_output[i], 0.0f) << "Negative at index " << i;
    }

    for (int r = 0; r < rows; r++) {
        float sum = 0.0f;
        for (int c = 0; c < cols; c++) {
            sum += h_output[r * cols + c];
        }
        EXPECT_NEAR(sum, 1.0f, 1e-4f);
    }

    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Numerical stability: large negative values should not produce NaN or Inf
 */
TEST_F(SoftmaxKernelTest, NumericalStability_NegativeLargeValues) {
    const int rows = 2;
    const int cols = 32;
    const int total = rows * cols;

    std::vector<float> h_input(total);
    for (int i = 0; i < total; i++) {
        h_input[i] = -500.0f + static_cast<float>(i) * 5.0f;
    }

    float* d_input = cuda_malloc<float>(total);
    float* d_output = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    transformer::launch_softmax(d_output, d_input, rows, cols, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total * sizeof(float), cudaMemcpyDeviceToHost));

    for (int i = 0; i < total; i++) {
        EXPECT_FALSE(std::isnan(h_output[i]));
        EXPECT_FALSE(std::isinf(h_output[i]));
    }

    for (int r = 0; r < rows; r++) {
        float sum = 0.0f;
        for (int c = 0; c < cols; c++) {
            sum += h_output[r * cols + c];
        }
        EXPECT_NEAR(sum, 1.0f, 1e-4f);
    }

    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Uniform input should produce uniform output (1/N for each element)
 */
TEST_F(SoftmaxKernelTest, UniformInput_UniformOutput) {
    const int rows = 2;
    const int cols = 16;
    const int total = rows * cols;

    std::vector<float> h_input(total, 3.14f);

    float* d_input = cuda_malloc<float>(total);
    float* d_output = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    transformer::launch_softmax(d_output, d_input, rows, cols, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total * sizeof(float), cudaMemcpyDeviceToHost));

    float expected = 1.0f / static_cast<float>(cols);
    for (int i = 0; i < total; i++) {
        EXPECT_NEAR(h_output[i], expected, 1e-5f)
            << "Non-uniform output at index " << i;
    }

    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Single-element rows should output 1.0
 */
TEST_F(SoftmaxKernelTest, SingleColumn_OutputOne) {
    const int rows = 4;
    const int cols = 1;
    const int total = rows * cols;

    std::vector<float> h_input = {-5.0f, 0.0f, 3.0f, 100.0f};

    float* d_input = cuda_malloc<float>(total);
    float* d_output = cuda_malloc<float>(total);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), total * sizeof(float), cudaMemcpyHostToDevice));

    transformer::launch_softmax(d_output, d_input, rows, cols, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total * sizeof(float), cudaMemcpyDeviceToHost));

    for (int i = 0; i < total; i++) {
        EXPECT_NEAR(h_output[i], 1.0f, 1e-5f);
    }

    cuda_free(d_input);
    cuda_free(d_output);
}
