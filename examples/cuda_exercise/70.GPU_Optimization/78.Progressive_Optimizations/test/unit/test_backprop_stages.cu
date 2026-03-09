/**
 * @file test_backprop_stages.cu
 * @brief Tests that all backprop optimization stages produce identical results.
 *
 * Verifies naive, fused, and optimized backpropagation implementations against
 * each other to ensure correctness is maintained across optimization levels.
 */
#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "backprop/01_naive.h"
#include "backprop/02_fused.h"
#include "backprop/03_optimized.h"
#include <vector>
#include <random>
#include <cmath>

/**
 * @brief Test fixture for backprop stage comparison tests.
 *
 * Provides helpers for generating random data and comparing gradient outputs.
 */
class BackpropStagesTest : public GpuTest {
protected:
    std::mt19937 gen{42};

    std::vector<float> randomVec(int n) {
        std::vector<float> m(n);
        std::uniform_real_distribution<float> dist(-0.5f, 0.5f);
        for (auto& v : m) v = dist(gen);
        return m;
    }

    bool compareVectors(const float* a, const float* b, int n, float tol = 1e-2f) {
        for (int i = 0; i < n; i++)
            if (std::abs(a[i] - b[i]) > tol) return false;
        return true;
    }
};

TEST_F(BackpropStagesTest, NaiveBackpropCorrectness) {
    const int batch = 8, in_feat = 32, out_feat = 16;
    auto grad_output = randomVec(batch * out_feat);
    auto input = randomVec(batch * in_feat);
    auto weight = randomVec(out_feat * in_feat);

    float *d_grad_output = cuda_malloc<float>(batch * out_feat);
    float *d_input = cuda_malloc<float>(batch * in_feat);
    float *d_weight = cuda_malloc<float>(out_feat * in_feat);
    float *d_grad_input = cuda_malloc<float>(batch * in_feat);
    float *d_grad_weight = cuda_malloc<float>(out_feat * in_feat);
    float *d_grad_bias = cuda_malloc<float>(out_feat);

    cuda_memcpy_h2d(d_grad_output, grad_output.data(), batch * out_feat);
    cuda_memcpy_h2d(d_input, input.data(), batch * in_feat);
    cuda_memcpy_h2d(d_weight, weight.data(), out_feat * in_feat);

    opt78::backprop_naive(d_grad_input, d_grad_weight, d_grad_bias,
                          d_grad_output, d_input, d_weight,
                          batch, in_feat, out_feat);
    CHECK_KERNEL_LAUNCH();

    // Verify grad_bias = sum(grad_output, dim=0)
    std::vector<float> h_grad_bias(out_feat);
    cuda_memcpy_d2h(h_grad_bias.data(), d_grad_bias, out_feat);
    for (int j = 0; j < out_feat; ++j) {
        float expected = 0.0f;
        for (int b = 0; b < batch; ++b)
            expected += grad_output[b * out_feat + j];
        EXPECT_NEAR(h_grad_bias[j], expected, 1e-3f)
            << "grad_bias[" << j << "] mismatch";
    }

    // Verify grad_input is non-zero
    std::vector<float> h_grad_input(batch * in_feat);
    cuda_memcpy_d2h(h_grad_input.data(), d_grad_input, batch * in_feat);
    float sum = 0;
    for (auto v : h_grad_input) sum += std::abs(v);
    EXPECT_GT(sum, 0.0f);

    cuda_free(d_grad_output); cuda_free(d_input); cuda_free(d_weight);
    cuda_free(d_grad_input); cuda_free(d_grad_weight); cuda_free(d_grad_bias);
}

TEST_F(BackpropStagesTest, FusedForwardBackward) {
    const int batch = 8, in_feat = 32, out_feat = 16;
    auto input = randomVec(batch * in_feat);
    auto weight = randomVec(out_feat * in_feat);
    auto bias = randomVec(out_feat);

    float *d_input = cuda_malloc<float>(batch * in_feat);
    float *d_weight = cuda_malloc<float>(out_feat * in_feat);
    float *d_bias = cuda_malloc<float>(out_feat);
    float *d_output = cuda_malloc<float>(batch * out_feat);
    float *d_relu_mask = cuda_malloc<float>(batch * out_feat);
    float *d_grad_output = cuda_malloc<float>(batch * out_feat);
    float *d_grad_input = cuda_malloc<float>(batch * in_feat);
    float *d_grad_weight = cuda_malloc<float>(out_feat * in_feat);
    float *d_grad_bias = cuda_malloc<float>(out_feat);

    cuda_memcpy_h2d(d_input, input.data(), batch * in_feat);
    cuda_memcpy_h2d(d_weight, weight.data(), out_feat * in_feat);
    cuda_memcpy_h2d(d_bias, bias.data(), out_feat);

    // Forward pass
    opt78::forward_fused(d_output, d_relu_mask, d_input, d_weight, d_bias,
                         batch, in_feat, out_feat);
    CHECK_KERNEL_LAUNCH();

    // Verify ReLU output
    std::vector<float> h_output(batch * out_feat);
    cuda_memcpy_d2h(h_output.data(), d_output, batch * out_feat);
    for (auto v : h_output)
        EXPECT_GE(v, 0.0f) << "ReLU output should be non-negative";

    // Use output as grad_output for backward
    cudaMemcpy(d_grad_output, d_output, batch * out_feat * sizeof(float), cudaMemcpyDeviceToDevice);

    opt78::backprop_fused(d_grad_input, d_grad_weight, d_grad_bias,
                          d_grad_output, d_input, d_weight, d_relu_mask,
                          batch, in_feat, out_feat);
    CHECK_KERNEL_LAUNCH();

    // Verify grad_weight is non-zero
    std::vector<float> h_grad_weight(out_feat * in_feat);
    cuda_memcpy_d2h(h_grad_weight.data(), d_grad_weight, out_feat * in_feat);
    float sum = 0.0f;
    for (auto v : h_grad_weight) sum += std::abs(v);
    EXPECT_GT(sum, 0.0f) << "grad_weight should be non-zero";

    cuda_free(d_input); cuda_free(d_weight); cuda_free(d_bias);
    cuda_free(d_output); cuda_free(d_relu_mask);
    cuda_free(d_grad_output); cuda_free(d_grad_input);
    cuda_free(d_grad_weight); cuda_free(d_grad_bias);
}

TEST_F(BackpropStagesTest, OptimizedMatchesNaive) {
    const int batch = 32, in_feat = 64, out_feat = 32;
    auto grad_output = randomVec(batch * out_feat);
    auto input = randomVec(batch * in_feat);
    auto weight = randomVec(out_feat * in_feat);
    std::vector<float> relu_mask(batch * out_feat, 1.0f);  // All-ones mask

    float *d_grad_output = cuda_malloc<float>(batch * out_feat);
    float *d_input = cuda_malloc<float>(batch * in_feat);
    float *d_weight = cuda_malloc<float>(out_feat * in_feat);
    float *d_relu_mask = cuda_malloc<float>(batch * out_feat);

    float *d_gi_naive = cuda_malloc<float>(batch * in_feat);
    float *d_gw_naive = cuda_malloc<float>(out_feat * in_feat);
    float *d_gb_naive = cuda_malloc<float>(out_feat);
    float *d_gi_opt = cuda_malloc<float>(batch * in_feat);
    float *d_gw_opt = cuda_malloc<float>(out_feat * in_feat);
    float *d_gb_opt = cuda_malloc<float>(out_feat);

    cuda_memcpy_h2d(d_grad_output, grad_output.data(), batch * out_feat);
    cuda_memcpy_h2d(d_input, input.data(), batch * in_feat);
    cuda_memcpy_h2d(d_weight, weight.data(), out_feat * in_feat);
    cuda_memcpy_h2d(d_relu_mask, relu_mask.data(), batch * out_feat);

    opt78::backprop_naive(d_gi_naive, d_gw_naive, d_gb_naive,
                          d_grad_output, d_input, d_weight,
                          batch, in_feat, out_feat);

    opt78::backprop_optimized(d_gi_opt, d_gw_opt, d_gb_opt,
                              d_grad_output, d_input, d_weight, d_relu_mask,
                              batch, in_feat, out_feat);
    CHECK_KERNEL_LAUNCH();

    std::vector<float> naive_gi(batch * in_feat), opt_gi(batch * in_feat);
    std::vector<float> naive_gw(out_feat * in_feat), opt_gw(out_feat * in_feat);
    std::vector<float> naive_gb(out_feat), opt_gb(out_feat);

    cuda_memcpy_d2h(naive_gi.data(), d_gi_naive, batch * in_feat);
    cuda_memcpy_d2h(opt_gi.data(), d_gi_opt, batch * in_feat);
    cuda_memcpy_d2h(naive_gw.data(), d_gw_naive, out_feat * in_feat);
    cuda_memcpy_d2h(opt_gw.data(), d_gw_opt, out_feat * in_feat);
    cuda_memcpy_d2h(naive_gb.data(), d_gb_naive, out_feat);
    cuda_memcpy_d2h(opt_gb.data(), d_gb_opt, out_feat);

    EXPECT_TRUE(compareVectors(naive_gi.data(), opt_gi.data(), batch * in_feat))
        << "grad_input: optimized differs from naive";
    EXPECT_TRUE(compareVectors(naive_gw.data(), opt_gw.data(), out_feat * in_feat))
        << "grad_weight: optimized differs from naive";
    EXPECT_TRUE(compareVectors(naive_gb.data(), opt_gb.data(), out_feat))
        << "grad_bias: optimized differs from naive";

    cuda_free(d_grad_output); cuda_free(d_input); cuda_free(d_weight); cuda_free(d_relu_mask);
    cuda_free(d_gi_naive); cuda_free(d_gw_naive); cuda_free(d_gb_naive);
    cuda_free(d_gi_opt); cuda_free(d_gw_opt); cuda_free(d_gb_opt);
}
