/**
 * @file benchmark.cu
 * @brief Benchmark program for CPU attention mechanism implementations
 *
 * Benchmarks naive, causal, and parallel SDPA at various sequence lengths,
 * reporting elapsed time and effective GFLOPS.
 */

#include "cpu_attention.h"
#include <iostream>
#include <iomanip>
#include <vector>
#include <cstring>
#include <cstdlib>

/// Print benchmark header banner
void print_header() {
    std::cout << "\n==========================================\n";
    std::cout << "  CPU Attention Mechanism Benchmark\n";
    std::cout << "==========================================\n\n";
}

/// Initialize Q, K, V matrices with random values
void initialize_matrices(float* Q, float* K, float* V, int seq_len, int d_model) {
    for (int i = 0; i < seq_len * d_model; i++) {
        Q[i] = static_cast<float>(rand()) / RAND_MAX;
        K[i] = static_cast<float>(rand()) / RAND_MAX;
        V[i] = static_cast<float>(rand()) / RAND_MAX;
    }
}

/// Run a single benchmark configuration and print results
void run_benchmark(const char* method, int seq_len, int d_model) {
    std::vector<float> Q(seq_len * d_model);
    std::vector<float> K(seq_len * d_model);
    std::vector<float> V(seq_len * d_model);
    std::vector<float> output(seq_len * d_model);

    initialize_matrices(Q.data(), K.data(), V.data(), seq_len, d_model);

    float elapsed_ms = cpu_attention_timed(output.data(), Q.data(), K.data(), V.data(),
                                           seq_len, d_model, method);

    // Calculate GFLOPS: 4*L*L*D + 5*L*L
    double flops = 4.0 * seq_len * seq_len * d_model + 5.0 * seq_len * seq_len;
    double gflops = flops / (elapsed_ms * 1e6);

    std::cout << std::setw(12) << method
              << " | " << std::setw(5) << seq_len << "x" << std::setw(3) << d_model
              << " | " << std::setw(10) << std::fixed << std::setprecision(2) << elapsed_ms << " ms"
              << " | " << std::setw(10) << std::fixed << std::setprecision(2) << gflops << " GFLOPS"
              << std::endl;
}

int main(int argc, char** argv) {
    print_header();

    int d_model = 64;
    std::vector<int> seq_lengths = {64, 128, 256, 512};

    if (argc > 1) {
        seq_lengths.clear();
        for (int i = 1; i < argc; i++) {
            seq_lengths.push_back(std::atoi(argv[i]));
        }
    }

    std::cout << "Model dimension (d_model): " << d_model << std::endl;
    std::cout << "Testing sequence lengths: ";
    for (int s : seq_lengths) {
        std::cout << s << " ";
    }
    std::cout << "\n\n";

    std::cout << std::setw(12) << "Method"
              << " | " << std::setw(10) << "Size"
              << " | " << std::setw(12) << "Time"
              << " | " << std::setw(12) << "Performance"
              << std::endl;
    std::cout << std::string(60, '-') << std::endl;

    for (int seq_len : seq_lengths) {
        run_benchmark("naive", seq_len, d_model);
        run_benchmark("causal", seq_len, d_model);
#ifdef HAS_OPENMP
        run_benchmark("parallel", seq_len, d_model);
#endif
        std::cout << std::endl;
    }

    std::cout << "\nBenchmark completed successfully!\n";
    return 0;
}
