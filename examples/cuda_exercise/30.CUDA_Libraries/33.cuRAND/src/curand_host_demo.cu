#include <curand.h>
#include "cuda_utils.h"
#include <iostream>
#include <memory>
#include <cmath>

void curand_uniform_demo() {
    std::cout << "\n=== Uniform Distribution ===\n";
    const int N = 1024 * 1024;

    curandGenerator_t gen;
    curandCreateGenerator(&gen, CURAND_RNG_PSEUDO_DEFAULT);
    curandSetPseudoRandomGeneratorSeed(gen, 1234ULL);

    float* d_random = cuda_malloc<float>(N);
    
    
    
    curandGenerateUniform(gen, d_random, N);
    cudaDeviceSynchronize();
    

    std::unique_ptr<float[]> h_random(new float[N]);
    cudaMemcpy(h_random.get(), d_random, N * sizeof(float), cudaMemcpyDeviceToHost);

    float sum = 0.0f, min_val = 1.0f, max_val = 0.0f;
    for (int i = 0; i < N; i++) {
        sum += h_random[i];
        min_val = std::min(min_val, h_random[i]);
        max_val = std::max(max_val, h_random[i]);
    }

    std::cout << "Generated " << N << " random numbers in " << 0.0f << " ms\n";
    std::cout << "Mean: " << sum / N << " (expected: 0.5)\n";
    std::cout << "Range: [" << min_val << ", " << max_val << "]\n";

    curandDestroyGenerator(gen);
    cuda_free(d_random);
}

void curand_normal_demo() {
    std::cout << "\n=== Normal Distribution ===\n";
    const int N = 1024 * 1024;

    curandGenerator_t gen;
    curandCreateGenerator(&gen, CURAND_RNG_PSEUDO_DEFAULT);
    curandSetPseudoRandomGeneratorSeed(gen, 1234ULL);

    float* d_random = cuda_malloc<float>(N);
    curandGenerateNormal(gen, d_random, N, 0.0f, 1.0f);
    cudaDeviceSynchronize();

    std::unique_ptr<float[]> h_random(new float[N]);
    cudaMemcpy(h_random.get(), d_random, N * sizeof(float), cudaMemcpyDeviceToHost);

    double mean = 0.0, variance = 0.0;
    for (int i = 0; i < N; i++) mean += h_random[i];
    mean /= N;
    
    for (int i = 0; i < N; i++) {
        double diff = h_random[i] - mean;
        variance += diff * diff;
    }
    variance /= N;

    std::cout << "Mean: " << mean << " (expected: 0.0)\n";
    std::cout << "Variance: " << variance << " (expected: 1.0)\n";

    curandDestroyGenerator(gen);
    cuda_free(d_random);
}

int main() {
    std::cout << "=== cuRAND Host API Demo ===\n";
    
    int device_count;
    cudaGetDeviceCount(&device_count);
    if (device_count == 0) {
        std::cerr << "No CUDA devices found!\n";
        return 1;
    }

    try {
        curand_uniform_demo();
        curand_normal_demo();
    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << "\n";
        return 1;
    }

    std::cout << "\nDemo completed successfully!\n";
    return 0;
}
