#include <cublas_v2.h>
#include <cuda_runtime.h>
#include <iostream>
#include <vector>
#include <random>
#include "cuda_utils.h"

// RAII wrapper for cuBLAS handle
class CublasHandle {
private:
    cublasHandle_t handle_;

public:
    CublasHandle() {
        cublasStatus_t status = cublasCreate(&handle_);
        if (status != CUBLAS_STATUS_SUCCESS) {
            throw std::runtime_error("Failed to create cuBLAS handle");
        }
    }

    ~CublasHandle() {
        cublasDestroy(handle_);
    }

    // Disable copy, enable move
    CublasHandle(const CublasHandle&) = delete;
    CublasHandle& operator=(const CublasHandle&) = delete;
    CublasHandle(CublasHandle&& other) noexcept : handle_(other.handle_) {
        other.handle_ = nullptr;
    }

    cublasHandle_t get() const { return handle_; }
};

// Simple naive matrix multiplication kernel for comparison
__global__ void matmul_naive(float* C, const float* A, const float* B, int N) {
    int row = blockIdx.y * blockDim.y + threadIdx.y;
    int col = blockIdx.x * blockDim.x + threadIdx.x;

    if (row < N && col < N) {
        float sum = 0.0f;
        for (int k = 0; k < N; k++) {
            sum += A[row * N + k] * B[k * N + col];
        }
        C[row * N + col] = sum;
    }
}

// Initialize matrix with random values
void initialize_random(float* d_data, int size) {
    std::vector<float> h_data(size);
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<float> dis(0.0f, 1.0f);

    for (int i = 0; i < size; i++) {
        h_data[i] = dis(gen);
    }

    cudaMemcpy(d_data, h_data.data(), size * sizeof(float), cudaMemcpyHostToDevice);
}

// Matrix multiply using cuBLAS: C = alpha * A * B + beta * C
void cublas_gemm(cublasHandle_t handle,
                 int m, int n, int k,
                 float alpha,
                 const float* A, int lda,
                 const float* B, int ldb,
                 float beta,
                 float* C, int ldc) {
    cublasSgemm(handle,
                CUBLAS_OP_N, CUBLAS_OP_N,
                m, n, k,
                &alpha,
                A, lda,
                B, ldb,
                &beta,
                C, ldc);
}

// Benchmark matrix multiplication
void benchmark_matmul(int N) {
    const int size = N * N;

    std::cout << "\n=== Matrix Multiplication Benchmark (N=" << N << ") ===\n\n";

    // Allocate matrices
    float *d_A = cuda_malloc<float>(size);
    float *d_B = cuda_malloc<float>(size);
    float *d_C_custom = cuda_malloc<float>(size);
    float *d_C_cublas = cuda_malloc<float>(size);

    // Initialize with random data
    initialize_random(d_A, size);
    initialize_random(d_B, size);

    CublasHandle handle;
    CudaTimer timer;

    // Benchmark custom naive kernel
    dim3 block(16, 16);
    dim3 grid((N + 15) / 16, (N + 15) / 16);

    timer.start();
    matmul_naive<<<grid, block>>>(d_C_custom, d_A, d_B, N);
    CHECK_KERNEL_LAUNCH();
    timer.stop();

    float custom_time = timer.elapsed_ms();
    float custom_gflops = (2.0f * N * N * N) / (custom_time * 1e6);

    std::cout << "Custom naive kernel:\n";
    std::cout << "  Performance: " << custom_gflops << " GFLOPS\n";
    std::cout << "  Time: " << custom_time << " ms\n\n";

    // Benchmark cuBLAS FP32
    float alpha = 1.0f, beta = 0.0f;

    // Warmup
    cublas_gemm(handle.get(), N, N, N, alpha, d_A, N, d_B, N, beta, d_C_cublas, N);
    cudaDeviceSynchronize();

    timer.start();
    cublas_gemm(handle.get(), N, N, N, alpha, d_A, N, d_B, N, beta, d_C_cublas, N);
    cudaDeviceSynchronize();
    timer.stop();

    float cublas_time = timer.elapsed_ms();
    float cublas_gflops = (2.0f * N * N * N) / (cublas_time * 1e6);

    std::cout << "cuBLAS FP32:\n";
    std::cout << "  Performance: " << cublas_gflops << " GFLOPS\n";
    std::cout << "  Time: " << cublas_time << " ms\n";
    std::cout << "  Speedup vs naive: " << (cublas_gflops / custom_gflops) << "x\n\n";

    // Check for Tensor Core support
    int device;
    cudaGetDevice(&device);
    cudaDeviceProp prop;
    cudaGetDeviceProperties(&prop, device);

    if (prop.major >= 7) {
        std::cout << "GPU supports Tensor Cores (compute capability "
                  << prop.major << "." << prop.minor << ")\n";
        std::cout << "Enable Tensor Cores with cublasSetMathMode(handle, CUBLAS_TENSOR_OP_MATH)\n";
        std::cout << "Use FP16 data for maximum performance\n";
    }

    // Cleanup
    cuda_free(d_A);
    cuda_free(d_B);
    cuda_free(d_C_custom);
    cuda_free(d_C_cublas);
}

// Verify correctness
bool verify_matmul(int N) {
    const int size = N * N;

    std::cout << "\n=== Correctness Verification (N=" << N << ") ===\n\n";

    // Host matrices
    std::vector<float> h_A(size);
    std::vector<float> h_B(size);
    std::vector<float> h_C_ref(size);
    std::vector<float> h_C_gpu(size);

    // Initialize with simple values
    for (int i = 0; i < size; i++) {
        h_A[i] = 1.0f;
        h_B[i] = 1.0f;
    }

    // CPU reference
    for (int i = 0; i < N; i++) {
        for (int j = 0; j < N; j++) {
            float sum = 0.0f;
            for (int k = 0; k < N; k++) {
                sum += h_A[i * N + k] * h_B[k * N + j];
            }
            h_C_ref[i * N + j] = sum;
        }
    }

    // GPU computation
    float *d_A = cuda_malloc<float>(size);
    float *d_B = cuda_malloc<float>(size);
    float *d_C = cuda_malloc<float>(size);

    cudaMemcpy(d_A, h_A.data(), size * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_B, h_B.data(), size * sizeof(float), cudaMemcpyHostToDevice);

    CublasHandle handle;
    float alpha = 1.0f, beta = 0.0f;

    // For row-major C = A * B, use column-major C^T = B^T * A^T
    cublasSgemm(handle.get(), CUBLAS_OP_N, CUBLAS_OP_N,
                N, N, N,
                &alpha,
                d_B, N,
                d_A, N,
                &beta,
                d_C, N);

    cudaMemcpy(h_C_gpu.data(), d_C, size * sizeof(float), cudaMemcpyDeviceToHost);

    // Verify
    bool correct = true;
    float max_error = 0.0f;
    for (int i = 0; i < size; i++) {
        float error = std::abs(h_C_ref[i] - h_C_gpu[i]);
        max_error = std::max(max_error, error);
        if (error > 1e-3f) {
            correct = false;
        }
    }

    if (correct) {
        std::cout << "✓ Verification PASSED\n";
        std::cout << "  Max error: " << max_error << "\n";
    } else {
        std::cout << "✗ Verification FAILED\n";
        std::cout << "  Max error: " << max_error << "\n";
    }

    cuda_free(d_A);
    cuda_free(d_B);
    cuda_free(d_C);

    return correct;
}
