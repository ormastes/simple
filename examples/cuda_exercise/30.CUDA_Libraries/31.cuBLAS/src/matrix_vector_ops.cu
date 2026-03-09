#include <cublas_v2.h>
#include <cuda_runtime.h>
#include <iostream>
#include <vector>
#include "cuda_utils.h"

// Level 2 BLAS Operations: Matrix-vector operations

// Matrix-vector multiply: y = alpha * A * x + beta * y
void cublas_gemv(cublasHandle_t handle,
                 int m, int n,
                 float alpha,
                 const float* A, int lda,
                 const float* x,
                 float beta,
                 float* y) {
    cublasSgemv(handle,
                CUBLAS_OP_N,  // No transpose
                m, n,
                &alpha,
                A, lda,
                x, 1,
                &beta,
                y, 1);
}

// Transpose matrix-vector: y = alpha * A^T * x + beta * y
void cublas_gemv_transpose(cublasHandle_t handle,
                           int m, int n,
                           float alpha,
                           const float* A, int lda,
                           const float* x,
                           float beta,
                           float* y) {
    cublasSgemv(handle,
                CUBLAS_OP_T,  // Transpose
                m, n,
                &alpha,
                A, lda,
                x, 1,
                &beta,
                y, 1);
}

// Demonstrate Level 2 BLAS operations
void demo_matrix_vector_ops(cublasHandle_t handle, int m, int n) {
    std::cout << "\n=== Level 2 BLAS Operations (m=" << m << ", n=" << n << ") ===\n\n";

    const int matrix_size = m * n;

    // Allocate device memory
    float *d_A = cuda_malloc<float>(matrix_size);
    float *d_x = cuda_malloc<float>(n);
    float *d_y = cuda_malloc<float>(m);

    // Initialize matrix and vector
    std::vector<float> h_A(matrix_size);
    std::vector<float> h_x(n);

    for (int i = 0; i < matrix_size; i++) {
        h_A[i] = static_cast<float>(i % 100) / 100.0f;
    }
    for (int i = 0; i < n; i++) {
        h_x[i] = 1.0f;
    }

    cudaMemcpy(d_A, h_A.data(), matrix_size * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_x, h_x.data(), n * sizeof(float), cudaMemcpyHostToDevice);

    CudaTimer timer;

    // Matrix-vector multiplication: y = A * x
    float alpha = 1.0f, beta = 0.0f;

    timer.start();
    cublas_gemv(handle, m, n, alpha, d_A, m, d_x, beta, d_y);
    cudaDeviceSynchronize();
    timer.stop();

    float gflops = (2.0f * m * n) / (timer.elapsed_ms() * 1e6);

    std::cout << "GEMV (y = A * x):\n";
    std::cout << "  Time: " << timer.elapsed_ms() << " ms\n";
    std::cout << "  Performance: " << gflops << " GFLOPS\n";
    std::cout << "  Bandwidth: " << ((matrix_size + n + m) * sizeof(float)) / (timer.elapsed_ms() * 1e6) << " GB/s\n\n";

    // Transpose matrix-vector: y = A^T * x
    float *d_x2 = cuda_malloc<float>(m);
    float *d_y2 = cuda_malloc<float>(n);

    std::vector<float> h_x2(m, 1.0f);
    cudaMemcpy(d_x2, h_x2.data(), m * sizeof(float), cudaMemcpyHostToDevice);

    timer.start();
    cublas_gemv_transpose(handle, m, n, alpha, d_A, m, d_x2, beta, d_y2);
    cudaDeviceSynchronize();
    timer.stop();

    gflops = (2.0f * m * n) / (timer.elapsed_ms() * 1e6);

    std::cout << "GEMV Transpose (y = A^T * x):\n";
    std::cout << "  Time: " << timer.elapsed_ms() << " ms\n";
    std::cout << "  Performance: " << gflops << " GFLOPS\n\n";

    // Cleanup
    cuda_free(d_A);
    cuda_free(d_x);
    cuda_free(d_y);
    cuda_free(d_x2);
    cuda_free(d_y2);
}
