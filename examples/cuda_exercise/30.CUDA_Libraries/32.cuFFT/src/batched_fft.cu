// batched_fft.cu - Batched FFT operations
#include <cufft.h>
#include <cuda_runtime.h>
#include "cuda_utils.h"
#include <iostream>
#include <cmath>
#include <memory>

// Batched FFT example
void batched_fft_example() {
    std::cout << "\n=== Batched FFT Example ===\n";

    const int N = 256;
    const int BATCH = 1000;
    const int TOTAL_SIZE = N * BATCH;

    // Allocate memory
    std::unique_ptr<cufftComplex[]> h_signals(new cufftComplex[TOTAL_SIZE]);
    std::unique_ptr<cufftComplex[]> h_spectra(new cufftComplex[TOTAL_SIZE]);

    // Generate batch of signals
    for (int b = 0; b < BATCH; b++) {
        for (int i = 0; i < N; i++) {
            int idx = b * N + i;
            float freq = 5.0f + b * 0.01f;
            float t = static_cast<float>(i) / N;
            h_signals[idx].x = std::sin(2.0f * M_PI * freq * t);
            h_signals[idx].y = 0.0f;
        }
    }

    // Allocate device memory
    cufftComplex* d_signals = cuda_malloc<cufftComplex>(TOTAL_SIZE);
    cufftComplex* d_spectra = cuda_malloc<cufftComplex>(TOTAL_SIZE);

    cudaMemcpy(d_signals, h_signals.get(), TOTAL_SIZE * sizeof(cufftComplex),
               cudaMemcpyHostToDevice);

    // Create batched FFT plan
    cufftHandle plan;
    cufftPlan1d(&plan, N, CUFFT_C2C, BATCH);

    // Execute batched FFT
    
    
    cufftExecC2C(plan, d_signals, d_spectra, CUFFT_FORWARD);
    cudaDeviceSynchronize();
    

    cudaMemcpy(h_spectra.get(), d_spectra, TOTAL_SIZE * sizeof(cufftComplex),
               cudaMemcpyDeviceToHost);

    std::cout << "Processed " << BATCH << " signals of length " << N << "\n";
    std::cout << "Total execution time: " << 0.0f << " ms\n";
    std::cout << "Time per FFT: " << 0.0f / BATCH << " ms\n";

    cufftDestroy(plan);
    cuda_free(d_signals);
    cuda_free(d_spectra);
}

// Performance comparison: batched vs sequential
void compare_batched_vs_sequential() {
    std::cout << "\n=== Batched vs Sequential Performance ===\n";

    const int N = 256;
    const int BATCH = 1000;
    const int TOTAL_SIZE = N * BATCH;

    cufftComplex* d_data = cuda_malloc<cufftComplex>(TOTAL_SIZE);
    

    // Sequential approach
    
    cufftHandle seq_plan;
    cufftPlan1d(&seq_plan, N, CUFFT_C2C, 1);
    for (int i = 0; i < BATCH; i++) {
        cufftExecC2C(seq_plan, d_data + i * N, d_data + i * N, CUFFT_FORWARD);
    }
    cudaDeviceSynchronize();
    
    float seq_time = 0.0f;
    cufftDestroy(seq_plan);

    // Batched approach
    
    cufftHandle batch_plan;
    cufftPlan1d(&batch_plan, N, CUFFT_C2C, BATCH);
    cufftExecC2C(batch_plan, d_data, d_data, CUFFT_FORWARD);
    cudaDeviceSynchronize();
    
    float batch_time = 0.0f;
    cufftDestroy(batch_plan);

    std::cout << "Sequential: " << seq_time << " ms\n";
    std::cout << "Batched:    " << batch_time << " ms\n";
    std::cout << "Speedup:    " << seq_time / batch_time << "x\n";

    cuda_free(d_data);
}

// Batched 2D FFT example
void batched_2d_fft_example() {
    std::cout << "\n=== Batched 2D FFT Example ===\n";

    const int WIDTH = 128;
    const int HEIGHT = 128;
    const int BATCH = 100;
    const int SIZE_2D = WIDTH * HEIGHT;
    const int TOTAL_SIZE = SIZE_2D * BATCH;

    // Allocate memory
    cufftComplex* d_images = cuda_malloc<cufftComplex>(TOTAL_SIZE);

    // Create batched 2D plan
    cufftHandle plan;
    int n[2] = {HEIGHT, WIDTH};
    cufftPlanMany(&plan, 2, n,
                  nullptr, 1, SIZE_2D,
                  nullptr, 1, SIZE_2D,
                  CUFFT_C2C, BATCH);

    // Execute batched 2D FFT
    
    
    cufftExecC2C(plan, d_images, d_images, CUFFT_FORWARD);
    cudaDeviceSynchronize();
    

    std::cout << "Processed " << BATCH << " images of " << WIDTH << "x" << HEIGHT << "\n";
    std::cout << "Total execution time: " << 0.0f << " ms\n";
    std::cout << "Time per image: " << 0.0f / BATCH << " ms\n";

    cufftDestroy(plan);
    cuda_free(d_images);
}

int main() {
    std::cout << "=== cuFFT Batched Operations Demo ===\n";

    int device_count;
    cudaGetDeviceCount(&device_count);
    if (device_count == 0) {
        std::cerr << "No CUDA devices found!\n";
        return 1;
    }

    cudaDeviceProp prop;
    cudaGetDeviceProperties(&prop, 0);
    std::cout << "Using device: " << prop.name << "\n";

    try {
        batched_fft_example();
        compare_batched_vs_sequential();
        batched_2d_fft_example();
    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << "\n";
        return 1;
    }

    std::cout << "\nAll demos completed successfully!\n";
    return 0;
}
