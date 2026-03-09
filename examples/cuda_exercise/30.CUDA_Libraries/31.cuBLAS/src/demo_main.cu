#include <cublas_v2.h>
#include <cuda_runtime.h>
#include <iostream>
#include "cuda_utils.h"

// External function declarations
extern void demo_vector_operations(cublasHandle_t handle, int n);
extern void demo_matrix_vector_ops(cublasHandle_t handle, int m, int n);
extern void benchmark_matmul(int N);
extern bool verify_matmul(int N);
extern void demo_batched_operations(cublasHandle_t handle, int M, int N, int K, int batch_count);

int main() {
    std::cout << "====================================\n";
    std::cout << "    cuBLAS Performance Demo\n";
    std::cout << "====================================\n\n";

    // Print device info
    int device;
    cudaGetDevice(&device);
    cudaDeviceProp prop;
    cudaGetDeviceProperties(&prop, device);

    std::cout << "GPU: " << prop.name << "\n";
    std::cout << "Compute Capability: " << prop.major << "." << prop.minor << "\n";
    std::cout << "Memory: " << (prop.totalGlobalMem / (1024 * 1024)) << " MB\n";

    if (prop.major >= 7) {
        std::cout << "Tensor Core support: YES\n";
    } else {
        std::cout << "Tensor Core support: NO\n";
    }
    std::cout << "\n";

    // Create cuBLAS handle
    cublasHandle_t handle;
    cublasCreate(&handle);

    try {
        // 1. Level 1 BLAS: Vector operations
        demo_vector_operations(handle, 1048576);  // 1M elements

        // 2. Level 2 BLAS: Matrix-vector operations
        demo_matrix_vector_ops(handle, 2048, 2048);

        // 3. Level 3 BLAS: Matrix multiplication
        verify_matmul(64);  // Small size for verification
        benchmark_matmul(1024);  // Medium size
        benchmark_matmul(2048);  // Large size

        // 4. Batched operations
        demo_batched_operations(handle, 128, 128, 128, 100);  // 100 small matrices

    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << "\n";
        cublasDestroy(handle);
        return 1;
    }

    cublasDestroy(handle);

    std::cout << "\n====================================\n";
    std::cout << "    Demo completed successfully\n";
    std::cout << "====================================\n";

    return 0;
}
