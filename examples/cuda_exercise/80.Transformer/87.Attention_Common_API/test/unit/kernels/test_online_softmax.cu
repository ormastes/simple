/**
 * @file test_online_softmax.cu
 * @brief Unit tests for online softmax primitives
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "common/online_softmax.cuh"
#include <vector>
#include <cmath>
#include <numeric>
#include <cfloat>

using namespace transformer;

/**
 * @brief Test fixture for online softmax tests with GPU setup
 */
class OnlineSoftmaxTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }

    /// CPU reference softmax for validation
    void cpu_softmax(std::vector<float>& data) {
        float max_val = *std::max_element(data.begin(), data.end());
        float sum = 0.0f;
        for (auto& v : data) {
            v = std::exp(v - max_val);
            sum += v;
        }
        for (auto& v : data) {
            v /= sum;
        }
    }
};

/**
 * @brief Kernel that runs online softmax on a single row and writes output
 */
__global__ void kernel_online_softmax_single_row(const float* __restrict__ input,
                                                  float* __restrict__ output,
                                                  int N) {
    // Build softmax state by streaming through all values
    SoftmaxState state;
    for (int i = 0; i < N; i++) {
        online_softmax_update(state, input[i]);
    }
    // Finalize: compute softmax probabilities
    for (int i = 0; i < N; i++) {
        output[i] = online_softmax_finalize(input[i], state);
    }
}

/**
 * @brief Kernel that tests merging two partial softmax states
 */
__global__ void kernel_online_softmax_merge_test(const float* __restrict__ input,
                                                  float* __restrict__ output,
                                                  int N, int split) {
    // Build state for first half
    SoftmaxState state_a;
    for (int i = 0; i < split; i++) {
        online_softmax_update(state_a, input[i]);
    }
    // Build state for second half
    SoftmaxState state_b;
    for (int i = split; i < N; i++) {
        online_softmax_update(state_b, input[i]);
    }
    // Merge
    SoftmaxState merged = online_softmax_merge(state_a, state_b);
    // Finalize
    for (int i = 0; i < N; i++) {
        output[i] = online_softmax_finalize(input[i], merged);
    }
}

/**
 * @brief Kernel that tests row_softmax (three-pass reference)
 */
__global__ void kernel_row_softmax(float* __restrict__ data, int N) {
    row_softmax(data, N);
}

/**
 * @brief Kernel that tests the rescale function
 */
__global__ void kernel_rescale_test(float* __restrict__ result,
                                     float old_val, float old_max, float new_max,
                                     float old_sum, float new_sum) {
    *result = online_softmax_rescale(old_val, old_max, new_max, old_sum, new_sum);
}

/**
 * @brief Test online softmax update/finalize against CPU reference
 */
TEST_F(OnlineSoftmaxTest, UpdateFinalize_MatchesCPU) {
    const int N = 128;
    std::vector<float> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = static_cast<float>(i) * 0.1f - 6.4f;
    }

    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), N * sizeof(float), cudaMemcpyHostToDevice));

    kernel_online_softmax_single_row<<<1, 1>>>(d_input, d_output, N);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(N);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, N * sizeof(float), cudaMemcpyDeviceToHost));

    // CPU reference
    std::vector<float> expected = h_input;
    cpu_softmax(expected);

    for (int i = 0; i < N; i++) {
        EXPECT_NEAR(h_output[i], expected[i], 1e-5f)
            << "Mismatch at index " << i;
    }

    // Verify probabilities sum to 1
    float sum = 0.0f;
    for (float v : h_output) sum += v;
    EXPECT_NEAR(sum, 1.0f, 1e-4f);

    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Test online softmax merge produces same result as single-pass
 */
TEST_F(OnlineSoftmaxTest, MergeStates_MatchesSinglePass) {
    const int N = 64;
    const int split = 20;

    std::vector<float> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = sinf(static_cast<float>(i) * 0.5f) * 3.0f;
    }

    float* d_input = cuda_malloc<float>(N);
    float* d_single = cuda_malloc<float>(N);
    float* d_merged = cuda_malloc<float>(N);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), N * sizeof(float), cudaMemcpyHostToDevice));

    kernel_online_softmax_single_row<<<1, 1>>>(d_input, d_single, N);
    kernel_online_softmax_merge_test<<<1, 1>>>(d_input, d_merged, N, split);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_single(N), h_merged(N);
    CHECK_CUDA(cudaMemcpy(h_single.data(), d_single, N * sizeof(float), cudaMemcpyDeviceToHost));
    CHECK_CUDA(cudaMemcpy(h_merged.data(), d_merged, N * sizeof(float), cudaMemcpyDeviceToHost));

    for (int i = 0; i < N; i++) {
        EXPECT_NEAR(h_merged[i], h_single[i], 1e-5f)
            << "Merge mismatch at index " << i;
    }

    cuda_free(d_input);
    cuda_free(d_single);
    cuda_free(d_merged);
}

/**
 * @brief Test numerical stability with large values (should not overflow/NaN)
 */
TEST_F(OnlineSoftmaxTest, NumericalStability_LargeValues) {
    const int N = 32;
    std::vector<float> h_input(N);
    // Use large values that would cause overflow in naive exp()
    for (int i = 0; i < N; i++) {
        h_input[i] = 500.0f + static_cast<float>(i) * 10.0f;
    }

    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), N * sizeof(float), cudaMemcpyHostToDevice));

    kernel_online_softmax_single_row<<<1, 1>>>(d_input, d_output, N);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(N);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, N * sizeof(float), cudaMemcpyDeviceToHost));

    // No NaN or Inf values
    for (int i = 0; i < N; i++) {
        EXPECT_FALSE(std::isnan(h_output[i])) << "NaN at index " << i;
        EXPECT_FALSE(std::isinf(h_output[i])) << "Inf at index " << i;
        EXPECT_GE(h_output[i], 0.0f) << "Negative probability at index " << i;
    }

    // Sum should be 1
    float sum = 0.0f;
    for (float v : h_output) sum += v;
    EXPECT_NEAR(sum, 1.0f, 1e-4f);

    // Largest input should have largest probability
    EXPECT_GT(h_output[N - 1], h_output[0]);

    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Test numerical stability with negative large values
 */
TEST_F(OnlineSoftmaxTest, NumericalStability_NegativeLargeValues) {
    const int N = 16;
    std::vector<float> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = -500.0f + static_cast<float>(i) * 5.0f;
    }

    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), N * sizeof(float), cudaMemcpyHostToDevice));

    kernel_online_softmax_single_row<<<1, 1>>>(d_input, d_output, N);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(N);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, N * sizeof(float), cudaMemcpyDeviceToHost));

    for (int i = 0; i < N; i++) {
        EXPECT_FALSE(std::isnan(h_output[i]));
        EXPECT_FALSE(std::isinf(h_output[i]));
    }

    float sum = 0.0f;
    for (float v : h_output) sum += v;
    EXPECT_NEAR(sum, 1.0f, 1e-4f);

    cuda_free(d_input);
    cuda_free(d_output);
}

/**
 * @brief Test row_softmax (three-pass) matches CPU reference
 */
TEST_F(OnlineSoftmaxTest, RowSoftmax_MatchesCPU) {
    const int N = 64;
    std::vector<float> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = cosf(static_cast<float>(i) * 0.3f) * 2.0f;
    }

    float* d_data = cuda_malloc<float>(N);
    CHECK_CUDA(cudaMemcpy(d_data, h_input.data(), N * sizeof(float), cudaMemcpyHostToDevice));

    kernel_row_softmax<<<1, 1>>>(d_data, N);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(N);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_data, N * sizeof(float), cudaMemcpyDeviceToHost));

    std::vector<float> expected = h_input;
    cpu_softmax(expected);

    for (int i = 0; i < N; i++) {
        EXPECT_NEAR(h_output[i], expected[i], 1e-5f);
    }

    cuda_free(d_data);
}

/**
 * @brief Test rescale function correctness
 */
TEST_F(OnlineSoftmaxTest, Rescale_Correctness) {
    float old_val = 2.0f;
    float old_max = 5.0f;
    float new_max = 7.0f;
    float old_sum = 10.0f;
    float new_sum = 15.0f;

    float expected = old_val * (std::exp(old_max - new_max) * old_sum / new_sum);

    float* d_result = cuda_malloc<float>(1);
    kernel_rescale_test<<<1, 1>>>(d_result, old_val, old_max, new_max, old_sum, new_sum);
    CHECK_CUDA(cudaDeviceSynchronize());

    float h_result;
    CHECK_CUDA(cudaMemcpy(&h_result, d_result, sizeof(float), cudaMemcpyDeviceToHost));

    EXPECT_NEAR(h_result, expected, 1e-5f);

    cuda_free(d_result);
}

/**
 * @brief Test uniform input (all same values produce uniform distribution)
 */
TEST_F(OnlineSoftmaxTest, UniformInput_UniformOutput) {
    const int N = 32;
    std::vector<float> h_input(N, 3.14f);

    float* d_input = cuda_malloc<float>(N);
    float* d_output = cuda_malloc<float>(N);
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(), N * sizeof(float), cudaMemcpyHostToDevice));

    kernel_online_softmax_single_row<<<1, 1>>>(d_input, d_output, N);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(N);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, N * sizeof(float), cudaMemcpyDeviceToHost));

    float expected_prob = 1.0f / static_cast<float>(N);
    for (int i = 0; i < N; i++) {
        EXPECT_NEAR(h_output[i], expected_prob, 1e-5f);
    }

    cuda_free(d_input);
    cuda_free(d_output);
}
