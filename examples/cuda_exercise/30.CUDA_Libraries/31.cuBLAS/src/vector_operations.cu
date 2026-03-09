#include <cublas_v2.h>
#include <cuda_runtime.h>
#include <iostream>
#include <vector>
#include "cuda_utils.h"

// Level 1 BLAS Operations: Vector-vector operations

// Dot product: result = x^T * y
float cublas_dot(cublasHandle_t handle, int n, const float* x, const float* y) {
    float result;
    cublasSdot(handle, n, x, 1, y, 1, &result);
    return result;
}

// Vector scaling: x = alpha * x
void cublas_scale(cublasHandle_t handle, int n, float alpha, float* x) {
    cublasSscal(handle, n, &alpha, x, 1);
}

// Vector addition: y = alpha * x + y  (AXPY)
void cublas_axpy(cublasHandle_t handle, int n, float alpha,
                 const float* x, float* y) {
    cublasSaxpy(handle, n, &alpha, x, 1, y, 1);
}

// L2 norm: result = ||x||_2
float cublas_nrm2(cublasHandle_t handle, int n, const float* x) {
    float result;
    cublasSnrm2(handle, n, x, 1, &result);
    return result;
}

// Copy vector: y = x
void cublas_copy(cublasHandle_t handle, int n, const float* x, float* y) {
    cublasScopy(handle, n, x, 1, y, 1);
}

// Demonstrate Level 1 BLAS operations
void demo_vector_operations(cublasHandle_t handle, int n) {
    std::cout << "\n=== Level 1 BLAS Operations (n=" << n << ") ===\n\n";

    // Allocate device vectors
    float *d_x = cuda_malloc<float>(n);
    float *d_y = cuda_malloc<float>(n);
    float *d_z = cuda_malloc<float>(n);

    // Initialize vectors
    std::vector<float> h_x(n);
    std::vector<float> h_y(n);

    for (int i = 0; i < n; i++) {
        h_x[i] = static_cast<float>(i + 1);
        h_y[i] = static_cast<float>(n - i);
    }

    cudaMemcpy(d_x, h_x.data(), n * sizeof(float), cudaMemcpyHostToDevice);
    cudaMemcpy(d_y, h_y.data(), n * sizeof(float), cudaMemcpyHostToDevice);

    CudaTimer timer;

    // Dot product
    timer.start();
    float dot_result = cublas_dot(handle, n, d_x, d_y);
    cudaDeviceSynchronize();
    timer.stop();

    std::cout << "Dot product (x^T * y):\n";
    std::cout << "  Result: " << dot_result << "\n";
    std::cout << "  Time: " << timer.elapsed_ms() << " ms\n";
    std::cout << "  Bandwidth: " << (2.0 * n * sizeof(float)) / (timer.elapsed_ms() * 1e6) << " GB/s\n\n";

    // Vector scaling
    float alpha = 2.0f;
    cublas_copy(handle, n, d_x, d_z);  // z = x

    timer.start();
    cublas_scale(handle, n, alpha, d_z);  // z = 2 * z
    cudaDeviceSynchronize();
    timer.stop();

    std::cout << "Vector scaling (alpha * x):\n";
    std::cout << "  alpha: " << alpha << "\n";
    std::cout << "  Time: " << timer.elapsed_ms() << " ms\n";
    std::cout << "  Bandwidth: " << (2.0 * n * sizeof(float)) / (timer.elapsed_ms() * 1e6) << " GB/s\n\n";

    // Vector addition (AXPY)
    alpha = 3.0f;
    cublas_copy(handle, n, d_x, d_z);  // Reset z = x

    timer.start();
    cublas_axpy(handle, n, alpha, d_x, d_z);  // z = 3*x + z = 4*x
    cudaDeviceSynchronize();
    timer.stop();

    std::cout << "Vector addition (alpha * x + y):\n";
    std::cout << "  alpha: " << alpha << "\n";
    std::cout << "  Time: " << timer.elapsed_ms() << " ms\n";
    std::cout << "  Bandwidth: " << (3.0 * n * sizeof(float)) / (timer.elapsed_ms() * 1e6) << " GB/s\n\n";

    // L2 norm
    timer.start();
    float norm_result = cublas_nrm2(handle, n, d_x);
    cudaDeviceSynchronize();
    timer.stop();

    std::cout << "L2 norm (||x||_2):\n";
    std::cout << "  Result: " << norm_result << "\n";
    std::cout << "  Time: " << timer.elapsed_ms() << " ms\n";
    std::cout << "  Bandwidth: " << (n * sizeof(float)) / (timer.elapsed_ms() * 1e6) << " GB/s\n\n";

    // Cleanup
    cuda_free(d_x);
    cuda_free(d_y);
    cuda_free(d_z);
}
