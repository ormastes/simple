/**
 * @file test_native_ops.cu
 * @brief GTest unit tests for native CUDA matmul, backprop, and attention kernels
 *
 * Tests the raw CUDA kernels (without PyTorch) to verify correctness of
 * matrix multiplication, linear backward pass, and scaled dot-product attention.
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "native_ops.h"
#include <vector>
#include <cmath>
#include <cstdlib>
#include <numeric>

/**
 * @brief Test fixture for native CUDA operator tests
 */
class NativeOpsTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }

    /// Fill vector with random values in [-1, 1]
    static void fill_random(std::vector<float>& v) {
        for (auto& x : v) {
            x = 2.0f * static_cast<float>(rand()) / RAND_MAX - 1.0f;
        }
    }

    /// CPU reference matmul: C[M x N] = A[M x K] * B[K x N]
    static void cpu_matmul(const float* A, const float* B, float* C,
                            int M, int N, int K) {
        for (int i = 0; i < M; ++i) {
            for (int j = 0; j < N; ++j) {
                float sum = 0.0f;
                for (int k = 0; k < K; ++k) {
                    sum += A[i * K + k] * B[k * N + j];
                }
                C[i * N + j] = sum;
            }
        }
    }
};

// ---- Matrix Multiplication Tests ----

/**
 * @brief Test tiled matmul against CPU reference for small matrices
 */
TEST_F(NativeOpsTest, MatMul_SmallSquare) {
    const int M = 16, N = 16, K = 16;

    std::vector<float> h_A(M * K), h_B(K * N), h_C(M * N, 0.0f), h_ref(M * N);
    fill_random(h_A);
    fill_random(h_B);
    cpu_matmul(h_A.data(), h_B.data(), h_ref.data(), M, N, K);

    float* d_A = cuda_malloc<float>(M * K);
    float* d_B = cuda_malloc<float>(K * N);
    float* d_C = cuda_malloc<float>(M * N);

    CHECK_CUDA(cudaMemcpy(d_A, h_A.data(), M * K * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_B, h_B.data(), K * N * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemset(d_C, 0, M * N * sizeof(float)));

    native_matmul(d_C, d_A, d_B, M, N, K);
    CHECK_CUDA(cudaDeviceSynchronize());

    CHECK_CUDA(cudaMemcpy(h_C.data(), d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost));

    for (int i = 0; i < M * N; ++i) {
        EXPECT_NEAR(h_C[i], h_ref[i], 1e-3f)
            << "Mismatch at index " << i;
    }

    cuda_free(d_A);
    cuda_free(d_B);
    cuda_free(d_C);
}

/**
 * @brief Test matmul with non-tile-aligned dimensions
 */
TEST_F(NativeOpsTest, MatMul_NonAligned) {
    const int M = 37, N = 53, K = 41;

    std::vector<float> h_A(M * K), h_B(K * N), h_C(M * N, 0.0f), h_ref(M * N);
    fill_random(h_A);
    fill_random(h_B);
    cpu_matmul(h_A.data(), h_B.data(), h_ref.data(), M, N, K);

    float* d_A = cuda_malloc<float>(M * K);
    float* d_B = cuda_malloc<float>(K * N);
    float* d_C = cuda_malloc<float>(M * N);

    CHECK_CUDA(cudaMemcpy(d_A, h_A.data(), M * K * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_B, h_B.data(), K * N * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemset(d_C, 0, M * N * sizeof(float)));

    native_matmul(d_C, d_A, d_B, M, N, K);
    CHECK_CUDA(cudaDeviceSynchronize());

    CHECK_CUDA(cudaMemcpy(h_C.data(), d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost));

    for (int i = 0; i < M * N; ++i) {
        EXPECT_NEAR(h_C[i], h_ref[i], 1e-2f)
            << "Mismatch at index " << i << " for non-aligned dimensions";
    }

    cuda_free(d_A);
    cuda_free(d_B);
    cuda_free(d_C);
}

/**
 * @brief Test matmul with larger tile-aligned dimensions
 */
TEST_F(NativeOpsTest, MatMul_LargerAligned) {
    const int M = 64, N = 128, K = 64;

    std::vector<float> h_A(M * K), h_B(K * N), h_C(M * N, 0.0f), h_ref(M * N);
    fill_random(h_A);
    fill_random(h_B);
    cpu_matmul(h_A.data(), h_B.data(), h_ref.data(), M, N, K);

    float* d_A = cuda_malloc<float>(M * K);
    float* d_B = cuda_malloc<float>(K * N);
    float* d_C = cuda_malloc<float>(M * N);

    CHECK_CUDA(cudaMemcpy(d_A, h_A.data(), M * K * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_B, h_B.data(), K * N * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemset(d_C, 0, M * N * sizeof(float)));

    native_matmul(d_C, d_A, d_B, M, N, K);
    CHECK_CUDA(cudaDeviceSynchronize());

    CHECK_CUDA(cudaMemcpy(h_C.data(), d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost));

    float max_err = 0.0f;
    for (int i = 0; i < M * N; ++i) {
        max_err = std::max(max_err, std::abs(h_C[i] - h_ref[i]));
    }
    EXPECT_LT(max_err, 0.05f) << "Max error too large for 64x128x64 matmul";

    std::cout << "MatMul 64x128x64 max error: " << max_err << std::endl;

    cuda_free(d_A);
    cuda_free(d_B);
    cuda_free(d_C);
}

// ---- Linear Backward Tests ----

/**
 * @brief Test linear backward computes non-zero gradients with correct bias gradient
 */
TEST_F(NativeOpsTest, LinearBackward_ProducesGradients) {
    const int batch = 8, in_f = 16, out_f = 32;

    std::vector<float> h_grad_output(batch * out_f);
    std::vector<float> h_input(batch * in_f);
    std::vector<float> h_weight(out_f * in_f);
    fill_random(h_grad_output);
    fill_random(h_input);
    fill_random(h_weight);

    float* d_grad_output = cuda_malloc<float>(batch * out_f);
    float* d_input = cuda_malloc<float>(batch * in_f);
    float* d_weight = cuda_malloc<float>(out_f * in_f);
    float* d_grad_input = cuda_malloc<float>(batch * in_f);
    float* d_grad_weight = cuda_malloc<float>(out_f * in_f);
    float* d_grad_bias = cuda_malloc<float>(out_f);

    CHECK_CUDA(cudaMemcpy(d_grad_output, h_grad_output.data(),
                         batch * out_f * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_input, h_input.data(),
                         batch * in_f * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_weight, h_weight.data(),
                         out_f * in_f * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemset(d_grad_input, 0, batch * in_f * sizeof(float)));
    CHECK_CUDA(cudaMemset(d_grad_weight, 0, out_f * in_f * sizeof(float)));
    CHECK_CUDA(cudaMemset(d_grad_bias, 0, out_f * sizeof(float)));

    native_linear_backward(d_grad_input, d_grad_weight, d_grad_bias,
                            d_grad_output, d_input, d_weight,
                            batch, in_f, out_f);
    CHECK_CUDA(cudaDeviceSynchronize());

    // Verify grad_input is non-zero
    std::vector<float> h_grad_input(batch * in_f);
    CHECK_CUDA(cudaMemcpy(h_grad_input.data(), d_grad_input,
                         batch * in_f * sizeof(float), cudaMemcpyDeviceToHost));
    float gi_max = 0.0f;
    for (auto v : h_grad_input) gi_max = std::max(gi_max, std::abs(v));
    EXPECT_GT(gi_max, 0.0f) << "grad_input is all zeros";

    // Verify grad_weight is non-zero
    std::vector<float> h_grad_weight(out_f * in_f);
    CHECK_CUDA(cudaMemcpy(h_grad_weight.data(), d_grad_weight,
                         out_f * in_f * sizeof(float), cudaMemcpyDeviceToHost));
    float gw_max = 0.0f;
    for (auto v : h_grad_weight) gw_max = std::max(gw_max, std::abs(v));
    EXPECT_GT(gw_max, 0.0f) << "grad_weight is all zeros";

    // Verify grad_bias matches column sum of grad_output
    std::vector<float> h_grad_bias(out_f);
    CHECK_CUDA(cudaMemcpy(h_grad_bias.data(), d_grad_bias,
                         out_f * sizeof(float), cudaMemcpyDeviceToHost));
    std::vector<float> ref_bias(out_f, 0.0f);
    for (int b = 0; b < batch; ++b) {
        for (int j = 0; j < out_f; ++j) {
            ref_bias[j] += h_grad_output[b * out_f + j];
        }
    }
    for (int j = 0; j < out_f; ++j) {
        EXPECT_NEAR(h_grad_bias[j], ref_bias[j], 1e-3f)
            << "grad_bias mismatch at index " << j;
    }

    std::cout << "LinearBackward grad magnitudes - input: " << gi_max
              << ", weight: " << gw_max << std::endl;

    cuda_free(d_grad_output);
    cuda_free(d_input);
    cuda_free(d_weight);
    cuda_free(d_grad_input);
    cuda_free(d_grad_weight);
    cuda_free(d_grad_bias);
}

// ---- Attention Tests ----

/**
 * @brief Test attention output has correct shape and finite values
 */
TEST_F(NativeOpsTest, Attention_ValidOutput) {
    const int seq_len = 16, head_dim = 8;

    std::vector<float> h_Q(seq_len * head_dim);
    std::vector<float> h_K(seq_len * head_dim);
    std::vector<float> h_V(seq_len * head_dim);
    fill_random(h_Q);
    fill_random(h_K);
    fill_random(h_V);

    float* d_Q = cuda_malloc<float>(seq_len * head_dim);
    float* d_K = cuda_malloc<float>(seq_len * head_dim);
    float* d_V = cuda_malloc<float>(seq_len * head_dim);
    float* d_O = cuda_malloc<float>(seq_len * head_dim);

    CHECK_CUDA(cudaMemcpy(d_Q, h_Q.data(), seq_len * head_dim * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_K, h_K.data(), seq_len * head_dim * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_V, h_V.data(), seq_len * head_dim * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemset(d_O, 0, seq_len * head_dim * sizeof(float)));

    native_attention(d_O, d_Q, d_K, d_V, seq_len, head_dim, /*causal=*/false);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_O(seq_len * head_dim);
    CHECK_CUDA(cudaMemcpy(h_O.data(), d_O, seq_len * head_dim * sizeof(float), cudaMemcpyDeviceToHost));

    // All output values should be finite
    int nan_count = 0;
    int inf_count = 0;
    for (size_t i = 0; i < h_O.size(); ++i) {
        if (std::isnan(h_O[i])) nan_count++;
        if (std::isinf(h_O[i])) inf_count++;
    }
    EXPECT_EQ(nan_count, 0) << "Attention output contains NaN";
    EXPECT_EQ(inf_count, 0) << "Attention output contains Inf";

    // Output should be non-zero (weighted combination of V)
    float max_abs = 0.0f;
    for (auto v : h_O) max_abs = std::max(max_abs, std::abs(v));
    EXPECT_GT(max_abs, 0.0f) << "Attention output is all zeros";

    std::cout << "Attention output max magnitude: " << max_abs << std::endl;

    cuda_free(d_Q);
    cuda_free(d_K);
    cuda_free(d_V);
    cuda_free(d_O);
}

/**
 * @brief Test causal attention produces finite output
 */
TEST_F(NativeOpsTest, Attention_CausalMask) {
    const int seq_len = 8, head_dim = 4;

    std::vector<float> h_Q(seq_len * head_dim);
    std::vector<float> h_K(seq_len * head_dim);
    std::vector<float> h_V(seq_len * head_dim);
    fill_random(h_Q);
    fill_random(h_K);
    fill_random(h_V);

    float* d_Q = cuda_malloc<float>(seq_len * head_dim);
    float* d_K = cuda_malloc<float>(seq_len * head_dim);
    float* d_V = cuda_malloc<float>(seq_len * head_dim);
    float* d_O = cuda_malloc<float>(seq_len * head_dim);

    CHECK_CUDA(cudaMemcpy(d_Q, h_Q.data(), seq_len * head_dim * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_K, h_K.data(), seq_len * head_dim * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_V, h_V.data(), seq_len * head_dim * sizeof(float), cudaMemcpyHostToDevice));

    // Run with causal mask
    native_attention(d_O, d_Q, d_K, d_V, seq_len, head_dim, /*causal=*/true);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_O(seq_len * head_dim);
    CHECK_CUDA(cudaMemcpy(h_O.data(), d_O, seq_len * head_dim * sizeof(float), cudaMemcpyDeviceToHost));

    // Output should be finite
    for (size_t i = 0; i < h_O.size(); ++i) {
        EXPECT_TRUE(std::isfinite(h_O[i]))
            << "Non-finite value at index " << i;
    }

    // Causal and non-causal should produce different results
    float* d_O_noncausal = cuda_malloc<float>(seq_len * head_dim);
    native_attention(d_O_noncausal, d_Q, d_K, d_V, seq_len, head_dim, /*causal=*/false);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_O_nc(seq_len * head_dim);
    CHECK_CUDA(cudaMemcpy(h_O_nc.data(), d_O_noncausal, seq_len * head_dim * sizeof(float), cudaMemcpyDeviceToHost));

    float max_diff = 0.0f;
    for (size_t i = 0; i < h_O.size(); ++i) {
        max_diff = std::max(max_diff, std::abs(h_O[i] - h_O_nc[i]));
    }
    EXPECT_GT(max_diff, 0.0f) << "Causal and non-causal attention produced identical results";

    std::cout << "Causal vs non-causal max diff: " << max_diff << std::endl;

    cuda_free(d_Q);
    cuda_free(d_K);
    cuda_free(d_V);
    cuda_free(d_O);
    cuda_free(d_O_noncausal);
}
