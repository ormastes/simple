/**
 * @file benchmark.cu
 * @brief Benchmark program for CPU Mixture of Experts implementations
 */

#include "cpu_experts.h"
#include <iostream>
#include <iomanip>
#include <vector>
#include <cstring>
#include <cstdlib>

void print_header() {
    std::cout << "\n============================================\n";
    std::cout << "  CPU Mixture of Experts (MoE) Benchmark\n";
    std::cout << "============================================\n\n";
}

void initialize_data(float* data, int size) {
    for (int i = 0; i < size; i++) {
        data[i] = static_cast<float>(rand()) / RAND_MAX * 0.1f;
    }
}

void run_benchmark(const char* method, int batch_size, int d_model, int d_ff,
                   int num_experts, int top_k) {
    // Allocate data
    std::vector<float> input(batch_size * d_model);
    std::vector<float> gate_weights(num_experts * d_model);
    std::vector<float> W1(num_experts * d_ff * d_model);
    std::vector<float> b1(num_experts * d_ff);
    std::vector<float> W2(num_experts * d_model * d_ff);
    std::vector<float> b2(num_experts * d_model);
    std::vector<float> output(batch_size * d_model);

    // Initialize
    initialize_data(input.data(), batch_size * d_model);
    initialize_data(gate_weights.data(), num_experts * d_model);
    initialize_data(W1.data(), num_experts * d_ff * d_model);
    initialize_data(b1.data(), num_experts * d_ff);
    initialize_data(W2.data(), num_experts * d_model * d_ff);
    initialize_data(b2.data(), num_experts * d_model);

    // Run benchmark
    float elapsed_ms = cpu_moe_timed(output.data(), input.data(), gate_weights.data(),
                                     W1.data(), b1.data(), W2.data(), b2.data(),
                                     batch_size, d_model, d_ff, num_experts, top_k,
                                     method);

    // Calculate GFLOPS
    double gate_flops = 2.0 * batch_size * num_experts * d_model;
    double expert_flops = 2.0 * batch_size * top_k * 2 * d_model * d_ff;
    double total_flops = gate_flops + expert_flops;
    double gflops = (total_flops / (elapsed_ms * 1e6));

    double sparsity = (1.0 - (double)top_k / num_experts) * 100;

    std::cout << std::setw(10) << method
              << " | B=" << std::setw(3) << batch_size
              << " D=" << std::setw(4) << d_model
              << " FF=" << std::setw(4) << d_ff
              << " E=" << std::setw(2) << num_experts
              << " K=" << std::setw(1) << top_k
              << " | " << std::setw(10) << std::fixed << std::setprecision(2) << elapsed_ms << " ms"
              << " | " << std::setw(8) << std::fixed << std::setprecision(2) << gflops << " GFLOPS"
              << " | " << std::setw(5) << std::fixed << std::setprecision(1) << sparsity << "%"
              << std::endl;
}

int main(int argc, char** argv) {
    print_header();

    struct Config {
        int batch_size, d_model, d_ff, num_experts, top_k;
    };

    std::vector<Config> configs = {
        {32, 128, 512, 4, 1},
        {32, 128, 512, 4, 2},
        {32, 128, 512, 8, 2},
        {32, 256, 1024, 8, 2},
        {32, 256, 1024, 16, 2},
    };

    std::cout << std::setw(10) << "Method"
              << " | " << std::setw(30) << "Configuration"
              << " | " << std::setw(12) << "Time"
              << " | " << std::setw(12) << "Performance"
              << " | " << std::setw(8) << "Sparsity"
              << std::endl;
    std::cout << std::string(85, '-') << std::endl;

    for (const auto& cfg : configs) {
        run_benchmark("naive", cfg.batch_size, cfg.d_model, cfg.d_ff,
                     cfg.num_experts, cfg.top_k);
#ifdef HAS_OPENMP
        run_benchmark("parallel", cfg.batch_size, cfg.d_model, cfg.d_ff,
                     cfg.num_experts, cfg.top_k);
#endif
        std::cout << std::endl;
    }

    std::cout << "\nBenchmark completed successfully!\n";
    return 0;
}
