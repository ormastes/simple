/**
 * @file benchmark.cu
 * @brief Benchmark program for CPU matrix multiplication implementations
 */

#include "cpu_matmul.h"
#include <iostream>
#include <iomanip>
#include <vector>
#include <cstring>

void print_header() {
    std::cout << "\n======================================\n";
    std::cout << "  CPU Matrix Multiplication Benchmark\n";
    std::cout << "======================================\n\n";
}

void initialize_matrices(float* A, float* B, int M, int N, int K) {
    for (int i = 0; i < M * K; i++) {
        A[i] = static_cast<float>(rand()) / RAND_MAX;
    }
    for (int i = 0; i < K * N; i++) {
        B[i] = static_cast<float>(rand()) / RAND_MAX;
    }
}

void run_benchmark(const char* method, int M, int N, int K) {
    // Allocate matrices
    std::vector<float> A(M * K);
    std::vector<float> B(K * N);
    std::vector<float> C(M * N);

    // Initialize
    initialize_matrices(A.data(), B.data(), M, N, K);

    // Run benchmark
    float elapsed_ms = cpu_matmul_timed(C.data(), A.data(), B.data(), M, N, K, method);

    // Calculate GFLOPS
    double gflops = (2.0 * M * N * K) / (elapsed_ms * 1e6);

    std::cout << std::setw(15) << method
              << " | " << std::setw(8) << M << "x" << N << "x" << K
              << " | " << std::setw(10) << std::fixed << std::setprecision(2) << elapsed_ms << " ms"
              << " | " << std::setw(10) << std::fixed << std::setprecision(2) << gflops << " GFLOPS"
              << std::endl;
}

int main(int argc, char** argv) {
    print_header();

    // Default matrix sizes
    std::vector<int> sizes = {128, 256, 512, 1024};

    if (argc > 1) {
        sizes.clear();
        for (int i = 1; i < argc; i++) {
            sizes.push_back(std::atoi(argv[i]));
        }
    }

    std::cout << "Testing matrix sizes: ";
    for (int size : sizes) {
        std::cout << size << "x" << size << " ";
    }
    std::cout << "\n\n";

    std::cout << std::setw(15) << "Method"
              << " | " << std::setw(15) << "Size"
              << " | " << std::setw(12) << "Time"
              << " | " << std::setw(12) << "Performance"
              << std::endl;
    std::cout << std::string(65, '-') << std::endl;

    for (int size : sizes) {
        run_benchmark("naive", size, size, size);
        run_benchmark("tiled", size, size, size);
#ifdef HAS_OPENMP
        run_benchmark("parallel", size, size, size);
#endif
        std::cout << std::endl;
    }

    std::cout << "\nBenchmark completed successfully!\n";
    return 0;
}
