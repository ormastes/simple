/**
 * @file test_cpu_matmul.cu
 * @brief Unit tests for CPU matrix multiplication
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cpu_matmul.h"
#include <vector>
#include <random>
#include <cmath>

/**
 * Test fixture for CPU MatMul tests
 */
class CPUMatMulTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Seed random number generator
        gen.seed(12345);
    }

    std::mt19937 gen;

    // Helper: Generate random matrix
    std::vector<float> randomMatrix(int rows, int cols) {
        std::vector<float> mat(rows * cols);
        std::uniform_real_distribution<float> dist(-1.0f, 1.0f);
        for (auto& val : mat) {
            val = dist(gen);
        }
        return mat;
    }

    // Helper: Compute reference result
    std::vector<float> referenceMatMul(const float* A, const float* B,
                                       int M, int N, int K) {
        std::vector<float> C(M * N);
        for (int i = 0; i < M; i++) {
            for (int j = 0; j < N; j++) {
                float sum = 0.0f;
                for (int k = 0; k < K; k++) {
                    sum += A[i * K + k] * B[k * N + j];
                }
                C[i * N + j] = sum;
            }
        }
        return C;
    }

    // Helper: Compare matrices
    bool matricesEqual(const float* A, const float* B, int size, float tol = 1e-4f) {
        for (int i = 0; i < size; i++) {
            if (std::abs(A[i] - B[i]) > tol) {
                return false;
            }
        }
        return true;
    }
};

/**
 * Test naive CPU matrix multiplication
 */
TEST_F(CPUMatMulTest, NaiveCorrectness) {
    const int M = 64, N = 64, K = 64;

    auto A = randomMatrix(M, K);
    auto B = randomMatrix(K, N);
    std::vector<float> C(M * N);

    cpu_matmul_naive(C.data(), A.data(), B.data(), M, N, K);

    auto C_ref = referenceMatMul(A.data(), B.data(), M, N, K);

    EXPECT_TRUE(matricesEqual(C.data(), C_ref.data(), M * N));
}

/**
 * Test small matrix
 */
TEST_F(CPUMatMulTest, SmallMatrix) {
    const int M = 4, N = 4, K = 4;

    std::vector<float> A = {
        1, 2, 3, 4,
        5, 6, 7, 8,
        9, 10, 11, 12,
        13, 14, 15, 16
    };

    std::vector<float> B = {
        1, 0, 0, 0,
        0, 1, 0, 0,
        0, 0, 1, 0,
        0, 0, 0, 1
    };  // Identity matrix

    std::vector<float> C(M * N);

    cpu_matmul_naive(C.data(), A.data(), B.data(), M, N, K);

    // C should equal A (since B is identity)
    EXPECT_TRUE(matricesEqual(C.data(), A.data(), M * N));
}

/**
 * Test tiled implementation
 */
TEST_F(CPUMatMulTest, TiledCorrectness) {
    const int M = 128, N = 128, K = 128;

    auto A = randomMatrix(M, K);
    auto B = randomMatrix(K, N);
    std::vector<float> C(M * N);

    cpu_matmul_tiled(C.data(), A.data(), B.data(), M, N, K, 64);

    auto C_ref = referenceMatMul(A.data(), B.data(), M, N, K);

    EXPECT_TRUE(matricesEqual(C.data(), C_ref.data(), M * N));
}

/**
 * Test parallel implementation
 */
TEST_F(CPUMatMulTest, ParallelCorrectness) {
    const int M = 128, N = 128, K = 128;

    auto A = randomMatrix(M, K);
    auto B = randomMatrix(K, N);
    std::vector<float> C(M * N);

    cpu_matmul_parallel(C.data(), A.data(), B.data(), M, N, K, 4);

    auto C_ref = referenceMatMul(A.data(), B.data(), M, N, K);

    EXPECT_TRUE(matricesEqual(C.data(), C_ref.data(), M * N));
}

/**
 * Test non-square matrices
 */
TEST_F(CPUMatMulTest, NonSquareMatrices) {
    const int M = 64, N = 128, K = 96;

    auto A = randomMatrix(M, K);
    auto B = randomMatrix(K, N);
    std::vector<float> C(M * N);

    cpu_matmul_naive(C.data(), A.data(), B.data(), M, N, K);

    auto C_ref = referenceMatMul(A.data(), B.data(), M, N, K);

    EXPECT_TRUE(matricesEqual(C.data(), C_ref.data(), M * N));
}

/**
 * Parameterized test for various sizes
 */
class MatMulSizeTest : public CPUMatMulTest,
                       public ::testing::WithParamInterface<std::tuple<int, int, int>> {};

TEST_P(MatMulSizeTest, VariousSizes) {
    auto [M, N, K] = GetParam();

    auto A = randomMatrix(M, K);
    auto B = randomMatrix(K, N);
    std::vector<float> C(M * N);

    cpu_matmul_naive(C.data(), A.data(), B.data(), M, N, K);

    auto C_ref = referenceMatMul(A.data(), B.data(), M, N, K);

    EXPECT_TRUE(matricesEqual(C.data(), C_ref.data(), M * N));
}

INSTANTIATE_TEST_SUITE_P(
    SizeVariations,
    MatMulSizeTest,
    ::testing::Values(
        std::make_tuple(16, 16, 16),
        std::make_tuple(32, 32, 32),
        std::make_tuple(64, 128, 64),
        std::make_tuple(128, 64, 128),
        std::make_tuple(256, 256, 256)
    )
);

/**
 * Performance benchmark test
 */
TEST_F(CPUMatMulTest, PerformanceBenchmark) {
    const int M = 512, N = 512, K = 512;

    auto A = randomMatrix(M, K);
    auto B = randomMatrix(K, N);
    std::vector<float> C(M * N);

    float time_ms = cpu_matmul_timed(C.data(), A.data(), B.data(), M, N, K, "naive");

    // Calculate GFLOPS
    double flops = 2.0 * M * N * K;  // 2 ops per multiply-add
    double gflops = (flops / (time_ms / 1000.0)) / 1e9;

    std::cout << "Matrix size: " << M << "×" << N << "×" << K << std::endl;
    std::cout << "Time: " << time_ms << " ms" << std::endl;
    std::cout << "Performance: " << gflops << " GFLOPS" << std::endl;

    // Sanity check: naive CPU implementation typically achieves 0.5-2 GFLOPS
    // depending on CPU architecture and cache behavior
    EXPECT_GT(gflops, 0.5) << "Performance too low for naive CPU matmul";
}
