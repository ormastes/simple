/**
 * @file test_gemm_wmma_tc.cu
 * @brief Unit tests for WMMA Tensor Core GEMM kernel correctness
 */
#include <gtest/gtest.h>
#include <cuda_runtime.h>
#include <cuda_fp16.h>
#include <vector>
#include <cmath>
#include <cstdlib>
#include "gpu_gtest.h"

// Forward declaration of launch function
namespace transformer {
void wmma_gemm_fp16(float* C, const half* A, const half* B,
                    int M, int N, int K, cudaStream_t stream);
} // namespace transformer

/**
 * @brief CPU reference GEMM in float for validation
 */
static void cpu_gemm_fp32(const float* A, const float* B, float* C, int M, int N, int K) {
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
 * @brief Check if current device supports WMMA (SM >= 7.0)
 */
static bool device_supports_wmma() {
    int device;
    cudaGetDevice(&device);
    cudaDeviceProp prop;
    cudaGetDeviceProperties(&prop, device);
    return (prop.major >= 7);
}

class WmmaGemmTest : public GpuTest {};

/**
 * @brief Test WMMA GEMM with 16x16 tile-aligned dimensions
 */
TEST_F(WmmaGemmTest, AlignedDimensions) {
    if (!device_supports_wmma()) {
        GTEST_SKIP() << "Device does not support WMMA (requires SM >= 7.0)";
    }

    const int M = 64, N = 64, K = 64;
    std::vector<float> h_A_fp32(M * K), h_B_fp32(K * N), h_C(M * N), h_ref(M * N);

    srand(42);
    for (auto& v : h_A_fp32) v = static_cast<float>(rand()) / RAND_MAX - 0.5f;
    for (auto& v : h_B_fp32) v = static_cast<float>(rand()) / RAND_MAX - 0.5f;

    // Convert to fp16 on host for reference computation
    std::vector<half> h_A_fp16(M * K), h_B_fp16(K * N);
    std::vector<float> h_A_quantized(M * K), h_B_quantized(K * N);
    for (int i = 0; i < M * K; i++) {
        h_A_fp16[i] = __float2half(h_A_fp32[i]);
        h_A_quantized[i] = __half2float(h_A_fp16[i]);
    }
    for (int i = 0; i < K * N; i++) {
        h_B_fp16[i] = __float2half(h_B_fp32[i]);
        h_B_quantized[i] = __half2float(h_B_fp16[i]);
    }

    // CPU reference using quantized values for fair comparison
    cpu_gemm_fp32(h_A_quantized.data(), h_B_quantized.data(), h_ref.data(), M, N, K);

    half *d_A;
    half *d_B;
    float *d_C;
    cudaMalloc(&d_A, M * K * sizeof(half));
    cudaMalloc(&d_B, K * N * sizeof(half));
    cudaMalloc(&d_C, M * N * sizeof(float));

    cudaMemcpy(d_A, h_A_fp16.data(), M * K * sizeof(half), cudaMemcpyHostToDevice);
    cudaMemcpy(d_B, h_B_fp16.data(), K * N * sizeof(half), cudaMemcpyHostToDevice);

    transformer::wmma_gemm_fp16(d_C, d_A, d_B, M, N, K, 0);
    cudaDeviceSynchronize();

    cudaMemcpy(h_C.data(), d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost);

    // fp16 accumulation allows larger tolerance
    for (int i = 0; i < M * N; i++) {
        ASSERT_NEAR(h_C[i], h_ref[i], 1e-1f * fabs(h_ref[i]) + 1e-2f)
            << "WMMA GEMM mismatch at index " << i;
    }

    cudaFree(d_A); cudaFree(d_B); cudaFree(d_C);
}

/**
 * @brief Test WMMA GEMM with larger matrices
 */
TEST_F(WmmaGemmTest, LargerMatrix) {
    if (!device_supports_wmma()) {
        GTEST_SKIP() << "Device does not support WMMA (requires SM >= 7.0)";
    }

    const int M = 128, N = 128, K = 128;
    std::vector<float> h_A_fp32(M * K), h_B_fp32(K * N), h_C(M * N), h_ref(M * N);

    srand(7);
    for (auto& v : h_A_fp32) v = (static_cast<float>(rand()) / RAND_MAX - 0.5f) * 0.1f;
    for (auto& v : h_B_fp32) v = (static_cast<float>(rand()) / RAND_MAX - 0.5f) * 0.1f;

    std::vector<half> h_A_fp16(M * K), h_B_fp16(K * N);
    std::vector<float> h_A_q(M * K), h_B_q(K * N);
    for (int i = 0; i < M * K; i++) {
        h_A_fp16[i] = __float2half(h_A_fp32[i]);
        h_A_q[i] = __half2float(h_A_fp16[i]);
    }
    for (int i = 0; i < K * N; i++) {
        h_B_fp16[i] = __float2half(h_B_fp32[i]);
        h_B_q[i] = __half2float(h_B_fp16[i]);
    }

    cpu_gemm_fp32(h_A_q.data(), h_B_q.data(), h_ref.data(), M, N, K);

    half *d_A;
    half *d_B;
    float *d_C;
    cudaMalloc(&d_A, M * K * sizeof(half));
    cudaMalloc(&d_B, K * N * sizeof(half));
    cudaMalloc(&d_C, M * N * sizeof(float));

    cudaMemcpy(d_A, h_A_fp16.data(), M * K * sizeof(half), cudaMemcpyHostToDevice);
    cudaMemcpy(d_B, h_B_fp16.data(), K * N * sizeof(half), cudaMemcpyHostToDevice);

    transformer::wmma_gemm_fp16(d_C, d_A, d_B, M, N, K, 0);
    cudaDeviceSynchronize();

    cudaMemcpy(h_C.data(), d_C, M * N * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < M * N; i++) {
        ASSERT_NEAR(h_C[i], h_ref[i], 1e-1f * fabs(h_ref[i]) + 1e-2f)
            << "WMMA large matrix mismatch at index " << i;
    }

    cudaFree(d_A); cudaFree(d_B); cudaFree(d_C);
}

/**
 * @brief Test WMMA GEMM identity: A * I = A
 */
TEST_F(WmmaGemmTest, IdentityMatrix) {
    if (!device_supports_wmma()) {
        GTEST_SKIP() << "Device does not support WMMA (requires SM >= 7.0)";
    }

    const int N = 16;
    std::vector<half> h_A(N * N), h_I(N * N);
    std::vector<float> h_C(N * N);

    // Create identity matrix
    for (int i = 0; i < N * N; i++) h_I[i] = __float2half(0.0f);
    for (int i = 0; i < N; i++) h_I[i * N + i] = __float2half(1.0f);

    // Random A
    srand(100);
    for (int i = 0; i < N * N; i++)
        h_A[i] = __float2half((static_cast<float>(rand()) / RAND_MAX - 0.5f) * 2.0f);

    half *d_A, *d_I;
    float *d_C;
    cudaMalloc(&d_A, N * N * sizeof(half));
    cudaMalloc(&d_I, N * N * sizeof(half));
    cudaMalloc(&d_C, N * N * sizeof(float));

    cudaMemcpy(d_A, h_A.data(), N * N * sizeof(half), cudaMemcpyHostToDevice);
    cudaMemcpy(d_I, h_I.data(), N * N * sizeof(half), cudaMemcpyHostToDevice);

    transformer::wmma_gemm_fp16(d_C, d_A, d_I, N, N, N, 0);
    cudaDeviceSynchronize();

    cudaMemcpy(h_C.data(), d_C, N * N * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < N * N; i++) {
        float expected = __half2float(h_A[i]);
        ASSERT_NEAR(h_C[i], expected, 1e-2f)
            << "Identity test mismatch at index " << i;
    }

    cudaFree(d_A); cudaFree(d_I); cudaFree(d_C);
}
