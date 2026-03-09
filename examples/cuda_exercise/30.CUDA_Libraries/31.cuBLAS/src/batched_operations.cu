#include <cublas_v2.h>
#include <cuda_runtime.h>
#include <iostream>
#include <vector>
#include "cuda_utils.h"

// Batched matrix multiplication: C[i] = A[i] * B[i] for all i
void cublas_gemm_batched(cublasHandle_t handle,
                         int m, int n, int k,
                         float alpha,
                         const float** A_array, int lda,
                         const float** B_array, int ldb,
                         float beta,
                         float** C_array, int ldc,
                         int batch_count) {
    cublasSgemmBatched(handle,
                       CUBLAS_OP_N, CUBLAS_OP_N,
                       m, n, k,
                       &alpha,
                       A_array, lda,
                       B_array, ldb,
                       &beta,
                       C_array, ldc,
                       batch_count);
}

// Demonstrate batched operations
void demo_batched_operations(cublasHandle_t handle, int M, int N, int K, int batch_count) {
    std::cout << "\n=== Batched Operations (M=" << M << ", N=" << N << ", K=" << K
              << ", batches=" << batch_count << ") ===\n\n";

    const int matrix_size_a = M * K;
    const int matrix_size_b = K * N;
    const int matrix_size_c = M * N;

    // Allocate batch of matrices
    std::vector<float*> h_A_ptrs(batch_count);
    std::vector<float*> h_B_ptrs(batch_count);
    std::vector<float*> h_C_ptrs(batch_count);

    for (int i = 0; i < batch_count; i++) {
        h_A_ptrs[i] = cuda_malloc<float>(matrix_size_a);
        h_B_ptrs[i] = cuda_malloc<float>(matrix_size_b);
        h_C_ptrs[i] = cuda_malloc<float>(matrix_size_c);

        // Initialize with simple pattern
        std::vector<float> h_A(matrix_size_a, 1.0f);
        std::vector<float> h_B(matrix_size_b, 1.0f);
        cudaMemcpy(h_A_ptrs[i], h_A.data(), matrix_size_a * sizeof(float), cudaMemcpyHostToDevice);
        cudaMemcpy(h_B_ptrs[i], h_B.data(), matrix_size_b * sizeof(float), cudaMemcpyHostToDevice);
    }

    // Copy pointer arrays to device
    float** d_A_ptrs = cuda_malloc<float*>(batch_count);
    float** d_B_ptrs = cuda_malloc<float*>(batch_count);
    float** d_C_ptrs = cuda_malloc<float*>(batch_count);

    cudaMemcpy(d_A_ptrs, h_A_ptrs.data(), batch_count * sizeof(float*), cudaMemcpyHostToDevice);
    cudaMemcpy(d_B_ptrs, h_B_ptrs.data(), batch_count * sizeof(float*), cudaMemcpyHostToDevice);
    cudaMemcpy(d_C_ptrs, h_C_ptrs.data(), batch_count * sizeof(float*), cudaMemcpyHostToDevice);

    float alpha = 1.0f, beta = 0.0f;
    CudaTimer timer;

    // Benchmark individual GEMM calls
    timer.start();
    for (int i = 0; i < batch_count; i++) {
        cublasSgemm(handle, CUBLAS_OP_N, CUBLAS_OP_N,
                    M, N, K,
                    &alpha,
                    h_A_ptrs[i], M,
                    h_B_ptrs[i], K,
                    &beta,
                    h_C_ptrs[i], M);
    }
    cudaDeviceSynchronize();
    timer.stop();

    float individual_time = timer.elapsed_ms();
    float individual_gflops = (2.0f * M * N * K * batch_count) / (individual_time * 1e6);

    std::cout << "Individual GEMM calls:\n";
    std::cout << "  Total time: " << individual_time << " ms\n";
    std::cout << "  Performance: " << individual_gflops << " GFLOPS\n\n";

    // Benchmark batched GEMM
    timer.start();
    cublas_gemm_batched(handle, M, N, K, alpha,
                        const_cast<const float**>(d_A_ptrs), M,
                        const_cast<const float**>(d_B_ptrs), K,
                        beta, d_C_ptrs, M, batch_count);
    cudaDeviceSynchronize();
    timer.stop();

    float batched_time = timer.elapsed_ms();
    float batched_gflops = (2.0f * M * N * K * batch_count) / (batched_time * 1e6);

    std::cout << "Batched GEMM:\n";
    std::cout << "  Total time: " << batched_time << " ms\n";
    std::cout << "  Performance: " << batched_gflops << " GFLOPS\n";
    std::cout << "  Speedup: " << (individual_time / batched_time) << "x\n\n";

    // Cleanup
    for (int i = 0; i < batch_count; i++) {
        cuda_free(h_A_ptrs[i]);
        cuda_free(h_B_ptrs[i]);
        cuda_free(h_C_ptrs[i]);
    }

    cuda_free(d_A_ptrs);
    cuda_free(d_B_ptrs);
    cuda_free(d_C_ptrs);
}
