/**
 * @file test_gemm_ops.cu
 * @brief Unit tests for the GEMM dispatcher and epilogue fusion API
 */
#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/gemm_ops.cuh"
#include "common/epilogue_fusion.cuh"
#include <vector>
#include <cmath>
#include <cstdlib>

// ---------------------------------------------------------------------------
// CPU reference implementations
// ---------------------------------------------------------------------------

static void cpu_matmul(float* C, const float* A, const float* B,
                       int M, int N, int K) {
    for (int i = 0; i < M; i++) {
        for (int j = 0; j < N; j++) {
            float sum = 0.0f;
            for (int k = 0; k < K; k++) {
                sum += A[i * K + k] * B[k * N + j];
            }
            C[i * N + j] = sum;
        }
    }
}

static float cpu_gelu(float x) {
    float cdf = 0.5f * (1.0f + tanhf(0.7978845608f * (x + 0.044715f * x * x * x)));
    return x * cdf;
}

static void cpu_add_bias(float* C, const float* bias, int M, int N) {
    for (int i = 0; i < M; i++) {
        for (int j = 0; j < N; j++) {
            C[i * N + j] += bias[j];
        }
    }
}

static void cpu_apply_gelu(float* C, int n) {
    for (int i = 0; i < n; i++) {
        C[i] = cpu_gelu(C[i]);
    }
}

static void fill_random(std::vector<float>& v, float lo = -1.0f, float hi = 1.0f) {
    for (auto& x : v) {
        x = lo + static_cast<float>(rand()) / RAND_MAX * (hi - lo);
    }
}

// ---------------------------------------------------------------------------
// Test fixture
// ---------------------------------------------------------------------------

class GemmOpsTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
        srand(42);
    }

    /// Helper: allocate device memory and copy host data
    float* to_device(const std::vector<float>& h_data) {
        float* d_ptr = nullptr;
        cudaMalloc(&d_ptr, h_data.size() * sizeof(float));
        cudaMemcpy(d_ptr, h_data.data(), h_data.size() * sizeof(float),
                   cudaMemcpyHostToDevice);
        return d_ptr;
    }

    /// Helper: copy device data to host
    std::vector<float> to_host(const float* d_ptr, int n) {
        std::vector<float> h_data(n);
        cudaMemcpy(h_data.data(), d_ptr, n * sizeof(float), cudaMemcpyDeviceToHost);
        return h_data;
    }
};

// ---------------------------------------------------------------------------
// Tests: SIMT GEMM correctness
// ---------------------------------------------------------------------------

TEST_F(GemmOpsTest, SimtGemm_Small_16x16) {
    const int M = 16, N = 16, K = 16;
    std::vector<float> h_A(M * K), h_B(K * N), h_C_ref(M * N);
    fill_random(h_A);
    fill_random(h_B);
    cpu_matmul(h_C_ref.data(), h_A.data(), h_B.data(), M, N, K);

    float* d_A = to_device(h_A);
    float* d_B = to_device(h_B);
    float* d_C = nullptr;
    cudaMalloc(&d_C, M * N * sizeof(float));
    cudaMemset(d_C, 0, M * N * sizeof(float));

    transformer::GemmParams params{};
    params.M = M; params.N = N; params.K = K;
    params.A_fp32 = d_A; params.B_fp32 = d_B; params.C = d_C;
    params.A_fp16 = nullptr; params.B_fp16 = nullptr;
    params.use_tensor_cores = false;
    params.stream = 0;
    transformer::gemm(params);
    cudaDeviceSynchronize();

    auto h_C = to_host(d_C, M * N);
    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C[i], h_C_ref[i], 1e-3f)
            << "Mismatch at index " << i;
    }

    cudaFree(d_A); cudaFree(d_B); cudaFree(d_C);
}

TEST_F(GemmOpsTest, SimtGemm_Medium_128x128) {
    const int M = 128, N = 128, K = 128;
    std::vector<float> h_A(M * K), h_B(K * N), h_C_ref(M * N);
    fill_random(h_A);
    fill_random(h_B);
    cpu_matmul(h_C_ref.data(), h_A.data(), h_B.data(), M, N, K);

    float* d_A = to_device(h_A);
    float* d_B = to_device(h_B);
    float* d_C = nullptr;
    cudaMalloc(&d_C, M * N * sizeof(float));
    cudaMemset(d_C, 0, M * N * sizeof(float));

    transformer::GemmParams params{};
    params.M = M; params.N = N; params.K = K;
    params.A_fp32 = d_A; params.B_fp32 = d_B; params.C = d_C;
    params.A_fp16 = nullptr; params.B_fp16 = nullptr;
    params.use_tensor_cores = false;
    params.stream = 0;
    transformer::gemm(params);
    cudaDeviceSynchronize();

    auto h_C = to_host(d_C, M * N);
    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C[i], h_C_ref[i], 0.5f)
            << "Mismatch at index " << i;
    }

    cudaFree(d_A); cudaFree(d_B); cudaFree(d_C);
}

TEST_F(GemmOpsTest, SimtGemm_NonSquare_64x128x96) {
    const int M = 64, N = 128, K = 96;
    std::vector<float> h_A(M * K), h_B(K * N), h_C_ref(M * N);
    fill_random(h_A);
    fill_random(h_B);
    cpu_matmul(h_C_ref.data(), h_A.data(), h_B.data(), M, N, K);

    float* d_A = to_device(h_A);
    float* d_B = to_device(h_B);
    float* d_C = nullptr;
    cudaMalloc(&d_C, M * N * sizeof(float));
    cudaMemset(d_C, 0, M * N * sizeof(float));

    transformer::GemmParams params{};
    params.M = M; params.N = N; params.K = K;
    params.A_fp32 = d_A; params.B_fp32 = d_B; params.C = d_C;
    params.A_fp16 = nullptr; params.B_fp16 = nullptr;
    params.use_tensor_cores = false;
    params.stream = 0;
    transformer::gemm(params);
    cudaDeviceSynchronize();

    auto h_C = to_host(d_C, M * N);
    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C[i], h_C_ref[i], 0.5f)
            << "Mismatch at index " << i;
    }

    cudaFree(d_A); cudaFree(d_B); cudaFree(d_C);
}

// ---------------------------------------------------------------------------
// Tests: GEMM with bias
// ---------------------------------------------------------------------------

TEST_F(GemmOpsTest, GemmWithBias) {
    const int M = 32, N = 64, K = 48;
    std::vector<float> h_A(M * K), h_B(K * N), h_bias(N), h_C_ref(M * N);
    fill_random(h_A);
    fill_random(h_B);
    fill_random(h_bias, -0.5f, 0.5f);

    cpu_matmul(h_C_ref.data(), h_A.data(), h_B.data(), M, N, K);
    cpu_add_bias(h_C_ref.data(), h_bias.data(), M, N);

    float* d_A = to_device(h_A);
    float* d_B = to_device(h_B);
    float* d_bias = to_device(h_bias);
    float* d_C = nullptr;
    cudaMalloc(&d_C, M * N * sizeof(float));

    transformer::gemm_with_bias_act(d_C, d_A, d_B, d_bias, M, N, K, false);
    cudaDeviceSynchronize();

    auto h_C = to_host(d_C, M * N);
    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C[i], h_C_ref[i], 0.5f)
            << "Mismatch at index " << i;
    }

    cudaFree(d_A); cudaFree(d_B); cudaFree(d_bias); cudaFree(d_C);
}

// ---------------------------------------------------------------------------
// Tests: GEMM with GELU activation
// ---------------------------------------------------------------------------

TEST_F(GemmOpsTest, GemmWithBiasAndGELU) {
    const int M = 32, N = 64, K = 48;
    std::vector<float> h_A(M * K), h_B(K * N), h_bias(N), h_C_ref(M * N);
    fill_random(h_A);
    fill_random(h_B);
    fill_random(h_bias, -0.5f, 0.5f);

    cpu_matmul(h_C_ref.data(), h_A.data(), h_B.data(), M, N, K);
    cpu_add_bias(h_C_ref.data(), h_bias.data(), M, N);
    cpu_apply_gelu(h_C_ref.data(), M * N);

    float* d_A = to_device(h_A);
    float* d_B = to_device(h_B);
    float* d_bias = to_device(h_bias);
    float* d_C = nullptr;
    cudaMalloc(&d_C, M * N * sizeof(float));

    transformer::gemm_with_bias_act(d_C, d_A, d_B, d_bias, M, N, K, true);
    cudaDeviceSynchronize();

    auto h_C = to_host(d_C, M * N);
    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_C[i], h_C_ref[i], 0.5f)
            << "Mismatch at index " << i;
    }

    cudaFree(d_A); cudaFree(d_B); cudaFree(d_bias); cudaFree(d_C);
}

// ---------------------------------------------------------------------------
// Tests: Convenience wrappers (linear, linear_gelu)
// ---------------------------------------------------------------------------

TEST_F(GemmOpsTest, LinearWrapper) {
    const int batch = 16, in_dim = 32, out_dim = 64;
    std::vector<float> h_input(batch * in_dim), h_weights(in_dim * out_dim);
    std::vector<float> h_bias(out_dim), h_C_ref(batch * out_dim);
    fill_random(h_input);
    fill_random(h_weights);
    fill_random(h_bias, -0.5f, 0.5f);

    cpu_matmul(h_C_ref.data(), h_input.data(), h_weights.data(), batch, out_dim, in_dim);
    cpu_add_bias(h_C_ref.data(), h_bias.data(), batch, out_dim);

    float* d_input = to_device(h_input);
    float* d_weights = to_device(h_weights);
    float* d_bias = to_device(h_bias);
    float* d_output = nullptr;
    cudaMalloc(&d_output, batch * out_dim * sizeof(float));

    transformer::linear(d_output, d_input, d_weights, d_bias, batch, in_dim, out_dim);
    cudaDeviceSynchronize();

    auto h_output = to_host(d_output, batch * out_dim);
    for (int i = 0; i < batch * out_dim; i++) {
        EXPECT_NEAR(h_output[i], h_C_ref[i], 0.5f)
            << "Mismatch at index " << i;
    }

    cudaFree(d_input); cudaFree(d_weights); cudaFree(d_bias); cudaFree(d_output);
}
