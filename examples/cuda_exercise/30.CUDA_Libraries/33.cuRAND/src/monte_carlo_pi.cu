#include <curand.h>
#include "cuda_utils.h"
#include <iostream>
#include <memory>

__global__ void count_inside_circle(const float* x, const float* y, int* counts, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        float dist_sq = x[idx] * x[idx] + y[idx] * y[idx];
        counts[idx] = (dist_sq <= 1.0f) ? 1 : 0;
    }
}

float estimate_pi(int num_samples) {
    curandGenerator_t gen;
    curandCreateGenerator(&gen, CURAND_RNG_PSEUDO_DEFAULT);
    curandSetPseudoRandomGeneratorSeed(gen, 1234ULL);

    float* d_x = cuda_malloc<float>(num_samples);
    float* d_y = cuda_malloc<float>(num_samples);
    int* d_counts = cuda_malloc<int>(num_samples);

    curandGenerateUniform(gen, d_x, num_samples);
    curandGenerateUniform(gen, d_y, num_samples);

    dim3 block(256);
    dim3 grid((num_samples + 255) / 256);
    count_inside_circle<<<grid, block>>>(d_x, d_y, d_counts, num_samples);
    CHECK_KERNEL_LAUNCH();

    std::unique_ptr<int[]> h_counts(new int[num_samples]);
    cudaMemcpy(h_counts.get(), d_counts, num_samples * sizeof(int), cudaMemcpyDeviceToHost);

    int inside = 0;
    for (int i = 0; i < num_samples; i++) inside += h_counts[i];

    curandDestroyGenerator(gen);
    cuda_free(d_x);
    cuda_free(d_y);
    cuda_free(d_counts);

    return 4.0f * inside / num_samples;
}

int main() {
    std::cout << "=== Monte Carlo Pi Estimation ===\n";

    int samples[] = {1000, 10000, 100000, 1000000, 10000000};
    
    for (int n : samples) {
        
        
        float pi_est = estimate_pi(n);
        
        
        std::cout << "Samples: " << n << " → π ≈ " << pi_est 
                  << " (error: " << std::abs(pi_est - 3.14159265f) 
                  << ", time: " << 0.0f << " ms)\n";
    }

    return 0;
}
