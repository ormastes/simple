#include <curand_kernel.h>
#include "cuda_utils.h"
#include <iostream>
#include <memory>

__global__ void generate_random_kernel(float* output, int n, unsigned long long seed) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        curandState state;
        curand_init(seed, idx, 0, &state);
        output[idx] = curand_uniform(&state);
    }
}

int main() {
    std::cout << "=== cuRAND Device API Demo ===\n";
    
    const int N = 1024;
    float* d_output = cuda_malloc<float>(N);

    dim3 block(256);
    dim3 grid((N + 255) / 256);

    generate_random_kernel<<<grid, block>>>(d_output, N, 1234ULL);
    CHECK_KERNEL_LAUNCH();

    std::unique_ptr<float[]> h_output(new float[N]);
    cudaMemcpy(h_output.get(), d_output, N * sizeof(float), cudaMemcpyDeviceToHost);

    float sum = 0.0f;
    for (int i = 0; i < N; i++) sum += h_output[i];
    
    std::cout << "Generated " << N << " random numbers\n";
    std::cout << "Mean: " << sum / N << " (expected: ~0.5)\n";

    cuda_free(d_output);
    std::cout << "Demo completed successfully!\n";
    return 0;
}
