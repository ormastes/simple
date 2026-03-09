// test_wmma.cu - Unit tests for Tensor Core (WMMA) operations
#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include <cuda_fp16.h>
#include <mma.h>
#include <memory>

using namespace nvcuda;

// Simple WMMA kernel for testing
__global__ void wmma_test_kernel(half* a, half* b, float* c, int M, int N, int K) {
    int warpM = (blockIdx.x * blockDim.x + threadIdx.x) / 32;
    int warpN = (blockIdx.y * blockDim.y + threadIdx.y);

    wmma::fragment<wmma::matrix_a, 16, 16, 16, half, wmma::row_major> a_frag;
    wmma::fragment<wmma::matrix_b, 16, 16, 16, half, wmma::row_major> b_frag;
    wmma::fragment<wmma::accumulator, 16, 16, 16, float> c_frag;

    wmma::fill_fragment(c_frag, 0.0f);

    if (warpM < M / 16 && warpN < N / 16) {
        // Accumulate along K dimension
        for (int k = 0; k < K; k += 16) {
            wmma::load_matrix_sync(a_frag, a + warpM * 16 * K + k, K);
            wmma::load_matrix_sync(b_frag, b + k * N + warpN * 16, N);
            wmma::mma_sync(c_frag, a_frag, b_frag, c_frag);
        }
        wmma::store_matrix_sync(c + warpM * 16 * N + warpN * 16, c_frag, N, wmma::mem_row_major);
    }
}

class WmmaTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();

        // Check compute capability
        int device;
        cudaGetDevice(&device);
        cudaDeviceProp prop;
        cudaGetDeviceProperties(&prop, device);

        if (prop.major < 7) {
            GTEST_SKIP() << "Tensor Cores require compute capability 7.0+";
        }
    }
};

TEST_F(WmmaTest, BasicIdentityMatrix) {
    const int M = 16, N = 16, K = 16;

    std::unique_ptr<half[]> h_a(new half[M * K]);
    std::unique_ptr<half[]> h_b(new half[K * N]);
    std::unique_ptr<float[]> h_c(new float[M * N]);

    // A = Identity, B = ones
    for (int i = 0; i < M * K; i++) h_a[i] = __float2half(0.0f);
    for (int i = 0; i < M; i++) h_a[i * K + i] = __float2half(1.0f);

    for (int i = 0; i < K * N; i++) h_b[i] = __float2half(1.0f);

    half* d_a;
    half* d_b;
    float* d_c;

    cudaMalloc(&d_a, M * K * sizeof(half));
    cudaMalloc(&d_b, K * N * sizeof(half));
    cudaMalloc(&d_c, M * N * sizeof(float));

    cudaMemcpy(d_a, h_a.get(), M * K * sizeof(half), cudaMemcpyHostToDevice);
    cudaMemcpy(d_b, h_b.get(), K * N * sizeof(half), cudaMemcpyHostToDevice);

    dim3 grid(1, 1);
    dim3 block(32, 1);
    wmma_test_kernel<<<grid, block>>>(d_a, d_b, d_c, M, N, K);

    ASSERT_EQ(cudaGetLastError(), cudaSuccess);
    cudaDeviceSynchronize();

    cudaMemcpy(h_c.get(), d_c, M * N * sizeof(float), cudaMemcpyDeviceToHost);

    // Result should be identity * ones = ones
    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_c[i], 1.0f, 0.1f) << "Mismatch at index " << i;
    }

    cudaFree(d_a);
    cudaFree(d_b);
    cudaFree(d_c);
}

TEST_F(WmmaTest, AllOnesMultiplication) {
    const int M = 16, N = 16, K = 16;

    std::unique_ptr<half[]> h_a(new half[M * K]);
    std::unique_ptr<half[]> h_b(new half[K * N]);
    std::unique_ptr<float[]> h_c(new float[M * N]);

    // All elements = 1, so result should be K
    for (int i = 0; i < M * K; i++) h_a[i] = __float2half(1.0f);
    for (int i = 0; i < K * N; i++) h_b[i] = __float2half(1.0f);

    half* d_a;
    half* d_b;
    float* d_c;

    cudaMalloc(&d_a, M * K * sizeof(half));
    cudaMalloc(&d_b, K * N * sizeof(half));
    cudaMalloc(&d_c, M * N * sizeof(float));

    cudaMemcpy(d_a, h_a.get(), M * K * sizeof(half), cudaMemcpyHostToDevice);
    cudaMemcpy(d_b, h_b.get(), K * N * sizeof(half), cudaMemcpyHostToDevice);

    dim3 grid(1, 1);
    dim3 block(32, 1);
    wmma_test_kernel<<<grid, block>>>(d_a, d_b, d_c, M, N, K);

    ASSERT_EQ(cudaGetLastError(), cudaSuccess);
    cudaDeviceSynchronize();

    cudaMemcpy(h_c.get(), d_c, M * N * sizeof(float), cudaMemcpyDeviceToHost);

    // Each element should be K (sum of K ones)
    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_c[i], static_cast<float>(K), 0.1f) << "Mismatch at index " << i;
    }

    cudaFree(d_a);
    cudaFree(d_b);
    cudaFree(d_c);
}

TEST_F(WmmaTest, ScalarMultiplication) {
    const int M = 16, N = 16, K = 16;
    const float scalar = 2.5f;

    std::unique_ptr<half[]> h_a(new half[M * K]);
    std::unique_ptr<half[]> h_b(new half[K * N]);
    std::unique_ptr<float[]> h_c(new float[M * N]);

    // A = scalar * identity, B = ones
    for (int i = 0; i < M * K; i++) h_a[i] = __float2half(0.0f);
    for (int i = 0; i < M; i++) h_a[i * K + i] = __float2half(scalar);

    for (int i = 0; i < K * N; i++) h_b[i] = __float2half(1.0f);

    half* d_a;
    half* d_b;
    float* d_c;

    cudaMalloc(&d_a, M * K * sizeof(half));
    cudaMalloc(&d_b, K * N * sizeof(half));
    cudaMalloc(&d_c, M * N * sizeof(float));

    cudaMemcpy(d_a, h_a.get(), M * K * sizeof(half), cudaMemcpyHostToDevice);
    cudaMemcpy(d_b, h_b.get(), K * N * sizeof(half), cudaMemcpyHostToDevice);

    dim3 grid(1, 1);
    dim3 block(32, 1);
    wmma_test_kernel<<<grid, block>>>(d_a, d_b, d_c, M, N, K);

    ASSERT_EQ(cudaGetLastError(), cudaSuccess);
    cudaDeviceSynchronize();

    cudaMemcpy(h_c.get(), d_c, M * N * sizeof(float), cudaMemcpyDeviceToHost);

    // Result should be scalar * ones
    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_c[i], scalar, 0.1f) << "Mismatch at index " << i;
    }

    cudaFree(d_a);
    cudaFree(d_b);
    cudaFree(d_c);
}

TEST_F(WmmaTest, ZeroMatrix) {
    const int M = 16, N = 16, K = 16;

    std::unique_ptr<half[]> h_a(new half[M * K]);
    std::unique_ptr<half[]> h_b(new half[K * N]);
    std::unique_ptr<float[]> h_c(new float[M * N]);

    // A = zeros, B = anything
    for (int i = 0; i < M * K; i++) h_a[i] = __float2half(0.0f);
    for (int i = 0; i < K * N; i++) h_b[i] = __float2half(3.14f);

    half* d_a;
    half* d_b;
    float* d_c;

    cudaMalloc(&d_a, M * K * sizeof(half));
    cudaMalloc(&d_b, K * N * sizeof(half));
    cudaMalloc(&d_c, M * N * sizeof(float));

    cudaMemcpy(d_a, h_a.get(), M * K * sizeof(half), cudaMemcpyHostToDevice);
    cudaMemcpy(d_b, h_b.get(), K * N * sizeof(half), cudaMemcpyHostToDevice);

    dim3 grid(1, 1);
    dim3 block(32, 1);
    wmma_test_kernel<<<grid, block>>>(d_a, d_b, d_c, M, N, K);

    ASSERT_EQ(cudaGetLastError(), cudaSuccess);
    cudaDeviceSynchronize();

    cudaMemcpy(h_c.get(), d_c, M * N * sizeof(float), cudaMemcpyDeviceToHost);

    // Result should be zeros
    for (int i = 0; i < M * N; i++) {
        EXPECT_NEAR(h_c[i], 0.0f, 0.01f) << "Mismatch at index " << i;
    }

    cudaFree(d_a);
    cudaFree(d_b);
    cudaFree(d_c);
}

// CPU reference for larger matrix multiplication
void cpu_matmul(const half* a, const half* b, float* c, int M, int N, int K) {
    for (int i = 0; i < M; i++) {
        for (int j = 0; j < N; j++) {
            float sum = 0.0f;
            for (int k = 0; k < K; k++) {
                sum += __half2float(a[i * K + k]) * __half2float(b[k * N + j]);
            }
            c[i * N + j] = sum;
        }
    }
}

TEST_F(WmmaTest, LargerMatrixVsCPU) {
    const int M = 32, N = 32, K = 32;

    std::unique_ptr<half[]> h_a(new half[M * K]);
    std::unique_ptr<half[]> h_b(new half[K * N]);
    std::unique_ptr<float[]> h_c_gpu(new float[M * N]);
    std::unique_ptr<float[]> h_c_cpu(new float[M * N]);

    // Random initialization
    for (int i = 0; i < M * K; i++) h_a[i] = __float2half((rand() % 100) / 100.0f);
    for (int i = 0; i < K * N; i++) h_b[i] = __float2half((rand() % 100) / 100.0f);

    // CPU reference
    cpu_matmul(h_a.get(), h_b.get(), h_c_cpu.get(), M, N, K);

    half* d_a;
    half* d_b;
    float* d_c;

    cudaMalloc(&d_a, M * K * sizeof(half));
    cudaMalloc(&d_b, K * N * sizeof(half));
    cudaMalloc(&d_c, M * N * sizeof(float));

    cudaMemcpy(d_a, h_a.get(), M * K * sizeof(half), cudaMemcpyHostToDevice);
    cudaMemcpy(d_b, h_b.get(), K * N * sizeof(half), cudaMemcpyHostToDevice);

    // Need 2x2 grid for 32x32 matrix (each tile is 16x16)
    // warpM = (blockIdx.x * blockDim.x + threadIdx.x) / 32
    // warpN = blockIdx.y
    // For 32x32 matrices: need warpM in [0,1] and warpN in [0,1]
    dim3 grid(2, 2);  // 2 blocks in x, 2 in y
    dim3 block(32, 1);  // Each block has 1 warp
    wmma_test_kernel<<<grid, block>>>(d_a, d_b, d_c, M, N, K);

    ASSERT_EQ(cudaGetLastError(), cudaSuccess);
    cudaDeviceSynchronize();

    cudaMemcpy(h_c_gpu.get(), d_c, M * N * sizeof(float), cudaMemcpyDeviceToHost);

    // Compare with CPU
    float max_error = 0.0f;
    for (int i = 0; i < M * N; i++) {
        float error = std::abs(h_c_gpu[i] - h_c_cpu[i]);
        max_error = std::max(max_error, error);
    }

    EXPECT_LT(max_error, 0.5f) << "Maximum error vs CPU: " << max_error;

    cudaFree(d_a);
    cudaFree(d_b);
    cudaFree(d_c);
}
