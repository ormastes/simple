// fft_2d_demo.cu - 2D FFT for image processing
#include <cufft.h>
#include <cuda_runtime.h>
#include "cuda_utils.h"
#include <iostream>
#include <cmath>
#include <memory>

// Lowpass filter kernel
__global__ void apply_lowpass_filter(cufftComplex* spectrum,
                                     int width, int height,
                                     float cutoff_freq) {
    int x = blockIdx.x * blockDim.x + threadIdx.x;
    int y = blockIdx.y * blockDim.y + threadIdx.y;

    if (x < width && y < height) {
        // Calculate distance from DC
        int cx = x < width/2 ? x : x - width;
        int cy = y < height/2 ? y : y - height;
        float dist = sqrtf(static_cast<float>(cx*cx + cy*cy));

        // Apply ideal lowpass filter
        int idx = y * width + x;
        if (dist > cutoff_freq) {
            spectrum[idx].x = 0.0f;
            spectrum[idx].y = 0.0f;
        }
    }
}

// 2D FFT example
void fft_2d_example() {
    std::cout << "\n=== 2D FFT Example ===\n";

    const int WIDTH = 512;
    const int HEIGHT = 512;
    const int SIZE = WIDTH * HEIGHT;

    // Allocate memory
    std::unique_ptr<cufftComplex[]> h_image(new cufftComplex[SIZE]);
    std::unique_ptr<cufftComplex[]> h_spectrum(new cufftComplex[SIZE]);

    // Generate checkerboard pattern
    for (int y = 0; y < HEIGHT; y++) {
        for (int x = 0; x < WIDTH; x++) {
            int idx = y * WIDTH + x;
            bool isWhite = ((x / 32) + (y / 32)) % 2 == 0;
            h_image[idx].x = isWhite ? 1.0f : 0.0f;
            h_image[idx].y = 0.0f;
        }
    }

    // Allocate device memory
    cufftComplex* d_image = cuda_malloc<cufftComplex>(SIZE);
    cufftComplex* d_spectrum = cuda_malloc<cufftComplex>(SIZE);

    cudaMemcpy(d_image, h_image.get(), SIZE * sizeof(cufftComplex),
               cudaMemcpyHostToDevice);

    // Create 2D FFT plan
    cufftHandle plan;
    cufftPlan2d(&plan, HEIGHT, WIDTH, CUFFT_C2C);

    // Execute forward FFT
    
    
    cufftExecC2C(plan, d_image, d_spectrum, CUFFT_FORWARD);
    cudaDeviceSynchronize();
    

    cudaMemcpy(h_spectrum.get(), d_spectrum, SIZE * sizeof(cufftComplex),
               cudaMemcpyDeviceToHost);

    std::cout << "FFT execution time: " << 0.0f << " ms\n";
    std::cout << "DC component (average): " << h_spectrum[0].x / SIZE << "\n";

    // Find dominant frequencies
    std::cout << "Dominant frequencies detected:\n";
    for (int y = 0; y < 32; y++) {
        for (int x = 0; x < 32; x++) {
            int idx = y * WIDTH + x;
            float magnitude = std::sqrt(h_spectrum[idx].x * h_spectrum[idx].x +
                                       h_spectrum[idx].y * h_spectrum[idx].y);
            if (magnitude > 50000.0f && (x != 0 || y != 0)) {
                std::cout << "  (" << x << ", " << y << "): "
                          << magnitude << "\n";
            }
        }
    }

    cufftDestroy(plan);
    cuda_free(d_image);
    cuda_free(d_spectrum);
}

// Lowpass filtering demonstration
void fft_lowpass_filter_demo() {
    std::cout << "\n=== 2D Lowpass Filter Demo ===\n";

    const int WIDTH = 256;
    const int HEIGHT = 256;
    const int SIZE = WIDTH * HEIGHT;

    // Create noisy image
    std::unique_ptr<cufftComplex[]> h_image(new cufftComplex[SIZE]);
    std::unique_ptr<cufftComplex[]> h_filtered(new cufftComplex[SIZE]);

    for (int y = 0; y < HEIGHT; y++) {
        for (int x = 0; x < WIDTH; x++) {
            int idx = y * WIDTH + x;
            // Circle pattern with noise
            float dx = x - WIDTH/2.0f;
            float dy = y - HEIGHT/2.0f;
            float dist = std::sqrt(dx*dx + dy*dy);
            float signal = (dist < 50.0f) ? 1.0f : 0.0f;
            float noise = 0.1f * (static_cast<float>(rand()) / RAND_MAX - 0.5f);
            h_image[idx].x = signal + noise;
            h_image[idx].y = 0.0f;
        }
    }

    // Allocate device memory
    cufftComplex* d_image = cuda_malloc<cufftComplex>(SIZE);

    cudaMemcpy(d_image, h_image.get(), SIZE * sizeof(cufftComplex),
               cudaMemcpyHostToDevice);

    // Create plan
    cufftHandle plan;
    cufftPlan2d(&plan, HEIGHT, WIDTH, CUFFT_C2C);

    // Forward FFT
    cufftExecC2C(plan, d_image, d_image, CUFFT_FORWARD);

    // Apply lowpass filter
    float cutoff = 32.0f;
    dim3 block(16, 16);
    dim3 grid((WIDTH + 15) / 16, (HEIGHT + 15) / 16);
    apply_lowpass_filter<<<grid, block>>>(d_image, WIDTH, HEIGHT, cutoff);
    CHECK_KERNEL_LAUNCH();

    // Inverse FFT
    cufftExecC2C(plan, d_image, d_image, CUFFT_INVERSE);
    cudaDeviceSynchronize();

    cudaMemcpy(h_filtered.get(), d_image, SIZE * sizeof(cufftComplex),
               cudaMemcpyDeviceToHost);

    // Compute SNR improvement
    float signal_power = 0.0f, noise_before = 0.0f, noise_after = 0.0f;
    for (int i = 0; i < SIZE; i++) {
        float dx = (i % WIDTH) - WIDTH/2.0f;
        float dy = (i / WIDTH) - HEIGHT/2.0f;
        float dist = std::sqrt(dx*dx + dy*dy);
        float true_signal = (dist < 50.0f) ? 1.0f : 0.0f;

        signal_power += true_signal * true_signal;
        noise_before += (h_image[i].x - true_signal) * (h_image[i].x - true_signal);

        float filtered_val = h_filtered[i].x / SIZE;  // Normalize
        noise_after += (filtered_val - true_signal) * (filtered_val - true_signal);
    }

    float snr_before = 10.0f * std::log10(signal_power / noise_before);
    float snr_after = 10.0f * std::log10(signal_power / noise_after);

    std::cout << "Cutoff frequency: " << cutoff << "\n";
    std::cout << "SNR before filtering: " << snr_before << " dB\n";
    std::cout << "SNR after filtering: " << snr_after << " dB\n";
    std::cout << "SNR improvement: " << (snr_after - snr_before) << " dB\n";

    cufftDestroy(plan);
    cuda_free(d_image);
}

int main() {
    std::cout << "=== cuFFT 2D Demo ===\n";

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
        fft_2d_example();
        fft_lowpass_filter_demo();
    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << "\n";
        return 1;
    }

    std::cout << "\nAll demos completed successfully!\n";
    return 0;
}
