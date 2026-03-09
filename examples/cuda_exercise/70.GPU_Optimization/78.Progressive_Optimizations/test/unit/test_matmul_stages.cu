/**
 * @file test_matmul_stages.cu
 * @brief Tests that all matmul optimization stages produce identical results.
 *
 * Verifies correctness by comparing each GPU stage against a CPU reference,
 * and consistency by comparing all stages against each other.
 */
#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "matmul/01_naive.h"
#include "matmul/02_shared_memory.h"
#include "matmul/03_tiled.h"
#include "matmul/04_vectorized.h"
#include "matmul/05_wmma.h"
#include <vector>
#include <random>
#include <cmath>

/**
 * @brief Test fixture for matmul stage comparison tests.
 *
 * Uses GpuTest for automatic CUDA device setup/teardown and provides
 * helpers for random matrix generation and comparison.
 */
class MatmulStagesTest : public GpuTest {
protected:
    std::mt19937 gen{42};

    std::vector<float> randomMatrix(int rows, int cols) {
        std::vector<float> m(rows * cols);
        std::uniform_real_distribution<float> dist(-1.0f, 1.0f);
        for (auto& v : m) v = dist(gen);
        return m;
    }

    void cpuMatmul(float* C, const float* A, const float* B, int M, int N, int K) {
        for (int i = 0; i < M; i++)
            for (int j = 0; j < N; j++) {
                float s = 0.0f;
                for (int k = 0; k < K; k++) s += A[i * K + k] * B[k * N + j];
                C[i * N + j] = s;
            }
    }

    bool compareMatrices(const float* a, const float* b, int n, float tol = 1e-3f) {
        for (int i = 0; i < n; i++)
            if (std::abs(a[i] - b[i]) > tol) return false;
        return true;
    }
};

TEST_F(MatmulStagesTest, NaiveCorrectness) {
    const int M = 64, N = 64, K = 64;
    auto A = randomMatrix(M, K);
    auto B = randomMatrix(K, N);
    std::vector<float> C_ref(M * N), C_gpu(M * N);

    cpuMatmul(C_ref.data(), A.data(), B.data(), M, N, K);

    float *dA = cuda_malloc<float>(M * K), *dB = cuda_malloc<float>(K * N), *dC = cuda_malloc<float>(M * N);
    cuda_memcpy_h2d(dA, A.data(), M * K);
    cuda_memcpy_h2d(dB, B.data(), K * N);

    opt78::matmul_naive(dC, dA, dB, M, N, K);
    CHECK_KERNEL_LAUNCH();
    cuda_memcpy_d2h(C_gpu.data(), dC, M * N);

    EXPECT_TRUE(compareMatrices(C_ref.data(), C_gpu.data(), M * N));

    cuda_free(dA); cuda_free(dB); cuda_free(dC);
}

TEST_F(MatmulStagesTest, SharedMemoryCorrectness) {
    const int M = 64, N = 64, K = 64;
    auto A = randomMatrix(M, K);
    auto B = randomMatrix(K, N);
    std::vector<float> C_ref(M * N), C_gpu(M * N);

    cpuMatmul(C_ref.data(), A.data(), B.data(), M, N, K);

    float *dA = cuda_malloc<float>(M * K), *dB = cuda_malloc<float>(K * N), *dC = cuda_malloc<float>(M * N);
    cuda_memcpy_h2d(dA, A.data(), M * K);
    cuda_memcpy_h2d(dB, B.data(), K * N);

    opt78::matmul_shared_memory(dC, dA, dB, M, N, K);
    CHECK_KERNEL_LAUNCH();
    cuda_memcpy_d2h(C_gpu.data(), dC, M * N);

    EXPECT_TRUE(compareMatrices(C_ref.data(), C_gpu.data(), M * N));

    cuda_free(dA); cuda_free(dB); cuda_free(dC);
}

TEST_F(MatmulStagesTest, TiledCorrectness) {
    const int M = 64, N = 64, K = 64;
    auto A = randomMatrix(M, K);
    auto B = randomMatrix(K, N);
    std::vector<float> C_ref(M * N), C_gpu(M * N);

    cpuMatmul(C_ref.data(), A.data(), B.data(), M, N, K);

    float *dA = cuda_malloc<float>(M * K), *dB = cuda_malloc<float>(K * N), *dC = cuda_malloc<float>(M * N);
    cuda_memcpy_h2d(dA, A.data(), M * K);
    cuda_memcpy_h2d(dB, B.data(), K * N);

    opt78::matmul_tiled(dC, dA, dB, M, N, K);
    CHECK_KERNEL_LAUNCH();
    cuda_memcpy_d2h(C_gpu.data(), dC, M * N);

    EXPECT_TRUE(compareMatrices(C_ref.data(), C_gpu.data(), M * N));

    cuda_free(dA); cuda_free(dB); cuda_free(dC);
}

TEST_F(MatmulStagesTest, VectorizedCorrectness) {
    const int M = 128, N = 128, K = 128;
    auto A = randomMatrix(M, K);
    auto B = randomMatrix(K, N);
    std::vector<float> C_ref(M * N), C_gpu(M * N);

    cpuMatmul(C_ref.data(), A.data(), B.data(), M, N, K);

    float *dA = cuda_malloc<float>(M * K), *dB = cuda_malloc<float>(K * N), *dC = cuda_malloc<float>(M * N);
    cuda_memcpy_h2d(dA, A.data(), M * K);
    cuda_memcpy_h2d(dB, B.data(), K * N);

    opt78::matmul_vectorized(dC, dA, dB, M, N, K);
    CHECK_KERNEL_LAUNCH();
    cuda_memcpy_d2h(C_gpu.data(), dC, M * N);

    EXPECT_TRUE(compareMatrices(C_ref.data(), C_gpu.data(), M * N, 1e-2f));

    cuda_free(dA); cuda_free(dB); cuda_free(dC);
}

TEST_F(MatmulStagesTest, WMMACorrectness) {
    int device;
    cudaGetDevice(&device);
    cudaDeviceProp prop;
    cudaGetDeviceProperties(&prop, device);
    if (prop.major < 7) {
        GTEST_SKIP() << "Tensor Cores require sm_70+, skipping WMMA test";
    }

    const int M = 128, N = 128, K = 128;
    auto A = randomMatrix(M, K);
    auto B = randomMatrix(K, N);
    std::vector<float> C_ref(M * N), C_gpu(M * N);

    cpuMatmul(C_ref.data(), A.data(), B.data(), M, N, K);

    float *dA = cuda_malloc<float>(M * K), *dB = cuda_malloc<float>(K * N), *dC = cuda_malloc<float>(M * N);
    cuda_memcpy_h2d(dA, A.data(), M * K);
    cuda_memcpy_h2d(dB, B.data(), K * N);

    opt78::matmul_wmma(dC, dA, dB, M, N, K);
    CHECK_KERNEL_LAUNCH();
    cuda_memcpy_d2h(C_gpu.data(), dC, M * N);

    // Higher tolerance due to fp16 intermediate precision
    EXPECT_TRUE(compareMatrices(C_ref.data(), C_gpu.data(), M * N, 1.0f));

    cuda_free(dA); cuda_free(dB); cuda_free(dC);
}

TEST_F(MatmulStagesTest, AllStagesMatch) {
    const int M = 128, N = 128, K = 128;
    auto A = randomMatrix(M, K);
    auto B = randomMatrix(K, N);

    float *dA = cuda_malloc<float>(M * K), *dB = cuda_malloc<float>(K * N), *dC = cuda_malloc<float>(M * N);
    cuda_memcpy_h2d(dA, A.data(), M * K);
    cuda_memcpy_h2d(dB, B.data(), K * N);

    // Get naive reference
    opt78::matmul_naive(dC, dA, dB, M, N, K);
    CHECK_KERNEL_LAUNCH();
    std::vector<float> C_naive(M * N);
    cuda_memcpy_d2h(C_naive.data(), dC, M * N);

    // Shared memory
    opt78::matmul_shared_memory(dC, dA, dB, M, N, K);
    CHECK_KERNEL_LAUNCH();
    std::vector<float> C_shared(M * N);
    cuda_memcpy_d2h(C_shared.data(), dC, M * N);
    EXPECT_TRUE(compareMatrices(C_naive.data(), C_shared.data(), M * N))
        << "Shared memory stage differs from naive";

    // Tiled
    opt78::matmul_tiled(dC, dA, dB, M, N, K);
    CHECK_KERNEL_LAUNCH();
    std::vector<float> C_tiled(M * N);
    cuda_memcpy_d2h(C_tiled.data(), dC, M * N);
    EXPECT_TRUE(compareMatrices(C_naive.data(), C_tiled.data(), M * N))
        << "Tiled stage differs from naive";

    // Vectorized
    opt78::matmul_vectorized(dC, dA, dB, M, N, K);
    CHECK_KERNEL_LAUNCH();
    std::vector<float> C_vec(M * N);
    cuda_memcpy_d2h(C_vec.data(), dC, M * N);
    EXPECT_TRUE(compareMatrices(C_naive.data(), C_vec.data(), M * N, 1e-2f))
        << "Vectorized stage differs from naive";

    cuda_free(dA); cuda_free(dB); cuda_free(dC);
}
