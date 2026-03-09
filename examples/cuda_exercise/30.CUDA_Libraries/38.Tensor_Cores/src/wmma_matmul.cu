// wmma_matmul.cu - Matrix multiplication using Tensor Cores
#include <mma.h>
#include <cuda_runtime.h>
#include <cuda_fp16.h>
#include "cuda_utils.h"
#include <iostream>
#include <memory>

using namespace nvcuda;

#define WMMA_M 16
#define WMMA_N 16
#define WMMA_K 16

// WMMA matrix multiplication kernel
__global__ void wmma_matmul_kernel(half* a, half* b, float* c, int M, int N, int K) {
    int warpM = (blockIdx.x * blockDim.x + threadIdx.x) / 32;
    int warpN = (blockIdx.y * blockDim.y + threadIdx.y);

    wmma::fragment<wmma::matrix_a, WMMA_M, WMMA_N, WMMA_K, half, wmma::row_major> a_frag;
    wmma::fragment<wmma::matrix_b, WMMA_M, WMMA_N, WMMA_K, half, wmma::row_major> b_frag;
    wmma::fragment<wmma::accumulator, WMMA_M, WMMA_N, WMMA_K, float> c_frag;

    wmma::fill_fragment(c_frag, 0.0f);

    if (warpM < M / WMMA_M && warpN < N / WMMA_N) {
        // Accumulate along K dimension
        for (int k = 0; k < K; k += WMMA_K) {
            wmma::load_matrix_sync(a_frag, a + warpM * WMMA_M * K + k, K);
            wmma::load_matrix_sync(b_frag, b + k * N + warpN * WMMA_N, N);
            wmma::mma_sync(c_frag, a_frag, b_frag, c_frag);
        }

        wmma::store_matrix_sync(c + warpM * WMMA_M * N + warpN * WMMA_N, c_frag, N, wmma::mem_row_major);
    }
}

// CPU reference implementation
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

int main() {
    std::cout << "=== Tensor Cores Matrix Multiplication ===\n";

    int device;
    cudaGetDevice(&device);
    cudaDeviceProp prop;
    cudaGetDeviceProperties(&prop, device);
    
    if (prop.major < 7) {
        std::cout << "Tensor Cores require compute capability 7.0+\n";
        return 0;
    }

    // Matrix dimensions (multiples of 16)
    const int M = 128, N = 128, K = 64;

    std::cout << "Matrix sizes: " << M << "x" << K << " * " << K << "x" << N << " = " << M << "x" << N << "\n";

    // Allocate host memory
    std::unique_ptr<half[]> h_a(new half[M * K]);
    std::unique_ptr<half[]> h_b(new half[K * N]);
    std::unique_ptr<float[]> h_c_gpu(new float[M * N]);
    std::unique_ptr<float[]> h_c_cpu(new float[M * N]);

    // Initialize with random values
    for (int i = 0; i < M * K; i++) h_a[i] = __float2half((rand() % 100) / 100.0f);
    for (int i = 0; i < K * N; i++) h_b[i] = __float2half((rand() % 100) / 100.0f);

    // CPU reference
    cpu_matmul(h_a.get(), h_b.get(), h_c_cpu.get(), M, N, K);

    // Allocate device memory
    half* d_a = cuda_malloc<half>(M * K);
    half* d_b = cuda_malloc<half>(K * N);
    float* d_c = cuda_malloc<float>(M * N);

    cudaMemcpy(d_a, h_a.get(), M * K * sizeof(half), cudaMemcpyHostToDevice);
    cudaMemcpy(d_b, h_b.get(), K * N * sizeof(half), cudaMemcpyHostToDevice);

    // Launch kernel
    // Each block has 1 warp (32 threads), and each warp handles 1 tile
    // Need (M/WMMA_M) x (N/WMMA_N) tiles
    dim3 grid(M / WMMA_M, N / WMMA_N);
    dim3 block(32, 1);
    
    wmma_matmul_kernel<<<grid, block>>>(d_a, d_b, d_c, M, N, K);
    CHECK_KERNEL_LAUNCH();

    cudaMemcpy(h_c_gpu.get(), d_c, M * N * sizeof(float), cudaMemcpyDeviceToHost);

    // Verify correctness
    float max_error = 0.0f;
    for (int i = 0; i < M * N; i++) {
        float error = std::abs(h_c_gpu[i] - h_c_cpu[i]);
        max_error = std::max(max_error, error);
    }

    std::cout << "Maximum error vs CPU: " << max_error << "\n";
    std::cout << "Correctness: " << (max_error < 0.1f ? "PASSED" : "FAILED") << "\n";

    cuda_free(d_a);
    cuda_free(d_b);
    cuda_free(d_c);

    std::cout << "Demo completed successfully!\n";
    return 0;
}
