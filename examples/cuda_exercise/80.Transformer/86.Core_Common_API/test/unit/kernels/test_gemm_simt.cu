/**
 * @file test_gemm_simt.cu
 * @brief Unit tests for SIMT GEMM kernel correctness and epilogue fusion
 */
#include <gtest/gtest.h>
#include <cuda_runtime.h>
#include <vector>
#include <cmath>
#include <cstdlib>
#include "common/epilogue_kernels.cuh"
#include "gpu_gtest.h"

// Forward declaration of launch function
namespace transformer {
void simt_gemm_fp32(float* C, const float* A, const float* B,
                    int M, int N, int K, Epilogue ep,
                    const float* bias, const float* residual,
                    cudaStream_t stream);
} // namespace transformer

/**
 * @brief CPU reference GEMM for validation
 */
static void cpu_gemm(const float* A, const float* B, float* C, int M, int N, int K) {
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

/**
 * @brief CPU reference for GELU activation
 */
static float cpu_gelu(float x) {
    const float kSqrt2OverPi = 0.7978845608028654f;
    float cdf = 0.5f * (1.0f + tanhf(kSqrt2OverPi * (x + 0.044715f * x * x * x)));
    return x * cdf;
}

/**
 * @brief CPU reference for ReLU activation
 */
static float cpu_relu(float x) {
    return fmaxf(0.0f, x);
}

class SimtGemmTest : public GpuTest {};

/**
 * @brief Test basic GEMM correctness with square matrices
 */
TEST_F(SimtGemmTest, SquareMatrix) {
    const int M = 64, N = 64, K = 64;
    std::vector<float> h_A(M * K), h_B(K * N), h_C(M * N), h_ref(M * N);

    srand(42);
    for (auto& v : h_A) v = static_cast<float>(rand()) / RAND_MAX - 0.5f;
    for (auto& v : h_B) v = static_cast<float>(rand()) / RAND_MAX - 0.5f;

    cpu_gemm(h_A.data(), h_B.data(), h_ref.data(), M, N, K);

    float *d_A, *d_B, *d_C;
    cudaMalloc(&d_A, M * K * sizeof(float));
    cudaMalloc(&d_B, K * N * sizeof(float));
    cudaMalloc(&d_C, M * N * sizeof(float));

    cudaMemcpy(d_A, h_A.data(), M * K * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_B, h_B.data(), K * N * sizeof(float), cudaMemcpyHostToDevice);

    transformer::Epilogue ep;
    transformer::simt_gemm_fp32(d_C, d_A, d_B, M, N, K, ep, nullptr, nullptr, 0);
    cudaDeviceSynchronize();

    cudaMemcpy(h_C.data(), d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < M * N; i++) {
        ASSERT_NEAR(h_C[i], h_ref[i], 1e-3f * fabs(h_ref[i]) + 1e-5f)
            << "Mismatch at index " << i;
    }

    cudaFree(d_A); cudaFree(d_B); cudaFree(d_C);
}

/**
 * @brief Test GEMM with non-square, non-tile-aligned dimensions
 */
TEST_F(SimtGemmTest, NonAlignedDimensions) {
    const int M = 37, N = 51, K = 19;
    std::vector<float> h_A(M * K), h_B(K * N), h_C(M * N), h_ref(M * N);

    srand(123);
    for (auto& v : h_A) v = static_cast<float>(rand()) / RAND_MAX - 0.5f;
    for (auto& v : h_B) v = static_cast<float>(rand()) / RAND_MAX - 0.5f;

    cpu_gemm(h_A.data(), h_B.data(), h_ref.data(), M, N, K);

    float *d_A, *d_B, *d_C;
    cudaMalloc(&d_A, M * K * sizeof(float));
    cudaMalloc(&d_B, K * N * sizeof(float));
    cudaMalloc(&d_C, M * N * sizeof(float));

    cudaMemcpy(d_A, h_A.data(), M * K * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_B, h_B.data(), K * N * sizeof(float), cudaMemcpyHostToDevice);

    transformer::Epilogue ep;
    transformer::simt_gemm_fp32(d_C, d_A, d_B, M, N, K, ep, nullptr, nullptr, 0);
    cudaDeviceSynchronize();

    cudaMemcpy(h_C.data(), d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < M * N; i++) {
        ASSERT_NEAR(h_C[i], h_ref[i], 1e-3f * fabs(h_ref[i]) + 1e-5f)
            << "Mismatch at index " << i << " (M=" << M << ", N=" << N << ", K=" << K << ")";
    }

    cudaFree(d_A); cudaFree(d_B); cudaFree(d_C);
}

/**
 * @brief Test GEMM with bias epilogue
 */
TEST_F(SimtGemmTest, EpilogueBias) {
    const int M = 32, N = 32, K = 32;
    std::vector<float> h_A(M * K), h_B(K * N), h_C(M * N), h_ref(M * N), h_bias(N);

    srand(99);
    for (auto& v : h_A) v = static_cast<float>(rand()) / RAND_MAX - 0.5f;
    for (auto& v : h_B) v = static_cast<float>(rand()) / RAND_MAX - 0.5f;
    for (auto& v : h_bias) v = static_cast<float>(rand()) / RAND_MAX - 0.5f;

    cpu_gemm(h_A.data(), h_B.data(), h_ref.data(), M, N, K);
    for (int i = 0; i < M; i++)
        for (int j = 0; j < N; j++)
            h_ref[i * N + j] += h_bias[j];

    float *d_A, *d_B, *d_C, *d_bias;
    cudaMalloc(&d_A, M * K * sizeof(float));
    cudaMalloc(&d_B, K * N * sizeof(float));
    cudaMalloc(&d_C, M * N * sizeof(float));
    cudaMalloc(&d_bias, N * sizeof(float));

    cudaMemcpy(d_A, h_A.data(), M * K * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_B, h_B.data(), K * N * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_bias, h_bias.data(), N * sizeof(float), cudaMemcpyHostToDevice);

    transformer::Epilogue ep;
    ep.has_bias = true;
    transformer::simt_gemm_fp32(d_C, d_A, d_B, M, N, K, ep, d_bias, nullptr, 0);
    cudaDeviceSynchronize();

    cudaMemcpy(h_C.data(), d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < M * N; i++) {
        ASSERT_NEAR(h_C[i], h_ref[i], 1e-3f * fabs(h_ref[i]) + 1e-5f)
            << "Bias epilogue mismatch at index " << i;
    }

    cudaFree(d_A); cudaFree(d_B); cudaFree(d_C); cudaFree(d_bias);
}

/**
 * @brief Test GEMM with ReLU activation epilogue
 */
TEST_F(SimtGemmTest, EpilogueReLU) {
    const int M = 32, N = 32, K = 32;
    std::vector<float> h_A(M * K), h_B(K * N), h_C(M * N), h_ref(M * N);

    srand(77);
    for (auto& v : h_A) v = static_cast<float>(rand()) / RAND_MAX - 0.5f;
    for (auto& v : h_B) v = static_cast<float>(rand()) / RAND_MAX - 0.5f;

    cpu_gemm(h_A.data(), h_B.data(), h_ref.data(), M, N, K);
    for (int i = 0; i < M * N; i++)
        h_ref[i] = cpu_relu(h_ref[i]);

    float *d_A, *d_B, *d_C;
    cudaMalloc(&d_A, M * K * sizeof(float));
    cudaMalloc(&d_B, K * N * sizeof(float));
    cudaMalloc(&d_C, M * N * sizeof(float));

    cudaMemcpy(d_A, h_A.data(), M * K * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_B, h_B.data(), K * N * sizeof(float), cudaMemcpyHostToDevice);

    transformer::Epilogue ep;
    ep.act = transformer::Activation::ReLU;
    transformer::simt_gemm_fp32(d_C, d_A, d_B, M, N, K, ep, nullptr, nullptr, 0);
    cudaDeviceSynchronize();

    cudaMemcpy(h_C.data(), d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < M * N; i++) {
        ASSERT_NEAR(h_C[i], h_ref[i], 1e-3f * fabs(h_ref[i]) + 1e-5f)
            << "ReLU epilogue mismatch at index " << i;
    }

    cudaFree(d_A); cudaFree(d_B); cudaFree(d_C);
}

/**
 * @brief Test GEMM with GELU activation epilogue
 */
TEST_F(SimtGemmTest, EpilogueGELU) {
    const int M = 32, N = 32, K = 32;
    std::vector<float> h_A(M * K), h_B(K * N), h_C(M * N), h_ref(M * N);

    srand(55);
    for (auto& v : h_A) v = static_cast<float>(rand()) / RAND_MAX - 0.5f;
    for (auto& v : h_B) v = static_cast<float>(rand()) / RAND_MAX - 0.5f;

    cpu_gemm(h_A.data(), h_B.data(), h_ref.data(), M, N, K);
    for (int i = 0; i < M * N; i++)
        h_ref[i] = cpu_gelu(h_ref[i]);

    float *d_A, *d_B, *d_C;
    cudaMalloc(&d_A, M * K * sizeof(float));
    cudaMalloc(&d_B, K * N * sizeof(float));
    cudaMalloc(&d_C, M * N * sizeof(float));

    cudaMemcpy(d_A, h_A.data(), M * K * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_B, h_B.data(), K * N * sizeof(float), cudaMemcpyHostToDevice);

    transformer::Epilogue ep;
    ep.act = transformer::Activation::GELU;
    transformer::simt_gemm_fp32(d_C, d_A, d_B, M, N, K, ep, nullptr, nullptr, 0);
    cudaDeviceSynchronize();

    cudaMemcpy(h_C.data(), d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < M * N; i++) {
        ASSERT_NEAR(h_C[i], h_ref[i], 1e-3f * fabs(h_ref[i]) + 1e-4f)
            << "GELU epilogue mismatch at index " << i;
    }

    cudaFree(d_A); cudaFree(d_B); cudaFree(d_C);
}

/**
 * @brief Test GEMM with full epilogue: bias + GELU + scale + residual
 */
TEST_F(SimtGemmTest, EpilogueFullFusion) {
    const int M = 32, N = 32, K = 32;
    std::vector<float> h_A(M * K), h_B(K * N), h_C(M * N), h_ref(M * N);
    std::vector<float> h_bias(N), h_residual(M * N);

    srand(33);
    for (auto& v : h_A) v = static_cast<float>(rand()) / RAND_MAX - 0.5f;
    for (auto& v : h_B) v = static_cast<float>(rand()) / RAND_MAX - 0.5f;
    for (auto& v : h_bias) v = static_cast<float>(rand()) / RAND_MAX - 0.5f;
    for (auto& v : h_residual) v = static_cast<float>(rand()) / RAND_MAX - 0.5f;

    const float scale = 0.5f;
    cpu_gemm(h_A.data(), h_B.data(), h_ref.data(), M, N, K);
    for (int i = 0; i < M; i++)
        for (int j = 0; j < N; j++) {
            int idx = i * N + j;
            float val = h_ref[idx] + h_bias[j];  // bias
            val = cpu_gelu(val);                   // activation
            val *= scale;                          // scale
            val += h_residual[idx];                // residual
            h_ref[idx] = val;
        }

    float *d_A, *d_B, *d_C, *d_bias, *d_residual;
    cudaMalloc(&d_A, M * K * sizeof(float));
    cudaMalloc(&d_B, K * N * sizeof(float));
    cudaMalloc(&d_C, M * N * sizeof(float));
    cudaMalloc(&d_bias, N * sizeof(float));
    cudaMalloc(&d_residual, M * N * sizeof(float));

    cudaMemcpy(d_A, h_A.data(), M * K * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_B, h_B.data(), K * N * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_bias, h_bias.data(), N * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_residual, h_residual.data(), M * N * sizeof(float), cudaMemcpyHostToDevice);

    transformer::Epilogue ep;
    ep.has_bias = true;
    ep.has_residual = true;
    ep.act = transformer::Activation::GELU;
    ep.scale = scale;
    transformer::simt_gemm_fp32(d_C, d_A, d_B, M, N, K, ep, d_bias, d_residual, 0);
    cudaDeviceSynchronize();

    cudaMemcpy(h_C.data(), d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < M * N; i++) {
        ASSERT_NEAR(h_C[i], h_ref[i], 1e-3f * fabs(h_ref[i]) + 1e-4f)
            << "Full fusion epilogue mismatch at index " << i;
    }

    cudaFree(d_A); cudaFree(d_B); cudaFree(d_C);
    cudaFree(d_bias); cudaFree(d_residual);
}
