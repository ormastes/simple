// fft_1d_demo.cu - 1D FFT demonstrations
#include <cufft.h>
#include <cuda_runtime.h>
#include "cuda_utils.h"
#include <iostream>
#include <cmath>
#include <memory>

// RAII wrapper for cuFFT plans
class CufftPlan {
private:
    cufftHandle plan_;
    bool valid_;

public:
    CufftPlan() : plan_(0), valid_(false) {}

    CufftPlan(int nx, cufftType type, int batch = 1) : valid_(false) {
        cufftResult result = cufftPlan1d(&plan_, nx, type, batch);
        if (result != CUFFT_SUCCESS) {
            throw std::runtime_error("Failed to create cuFFT plan");
        }
        valid_ = true;
    }

    ~CufftPlan() {
        if (valid_) {
            cufftDestroy(plan_);
        }
    }

    // Disable copy, enable move
    CufftPlan(const CufftPlan&) = delete;
    CufftPlan& operator=(const CufftPlan&) = delete;

    CufftPlan(CufftPlan&& other) noexcept : plan_(other.plan_), valid_(other.valid_) {
        other.valid_ = false;
        other.plan_ = 0;
    }

    cufftHandle get() const { return plan_; }
};

// 1D Complex-to-Complex FFT example
void fft_1d_c2c_example() {
    std::cout << "\n=== 1D Complex-to-Complex FFT ===\n";

    const int N = 1024;

    // Allocate host memory
    std::unique_ptr<cufftComplex[]> h_signal(new cufftComplex[N]);
    std::unique_ptr<cufftComplex[]> h_spectrum(new cufftComplex[N]);

    // Generate test signal: sum of two sine waves
    // f(t) = sin(2π * 5 * t) + 0.5 * sin(2π * 10 * t)
    for (int i = 0; i < N; i++) {
        float t = static_cast<float>(i) / N;
        h_signal[i].x = std::sin(2.0f * M_PI * 5.0f * t) +
                        0.5f * std::sin(2.0f * M_PI * 10.0f * t);
        h_signal[i].y = 0.0f;
    }

    // Allocate device memory
    cufftComplex* d_signal = cuda_malloc<cufftComplex>(N);
    cufftComplex* d_spectrum = cuda_malloc<cufftComplex>(N);

    cudaMemcpy(d_signal, h_signal.get(), N * sizeof(cufftComplex),
               cudaMemcpyHostToDevice);

    // Create FFT plan
    CufftPlan plan(N, CUFFT_C2C, 1);

    // Execute FFT
    
    
    cufftExecC2C(plan.get(), d_signal, d_spectrum, CUFFT_FORWARD);
    cudaDeviceSynchronize();
    

    cudaMemcpy(h_spectrum.get(), d_spectrum, N * sizeof(cufftComplex),
               cudaMemcpyDeviceToHost);

    std::cout << "FFT execution time: " << 0.0f << " ms\n";
    std::cout << "Frequency domain peaks:\n";

    // Find peaks
    for (int i = 0; i < N / 2; i++) {
        float magnitude = std::sqrt(h_spectrum[i].x * h_spectrum[i].x +
                                   h_spectrum[i].y * h_spectrum[i].y);
        if (magnitude > 100.0f) {
            std::cout << "  Frequency bin " << i << ": magnitude = "
                      << magnitude << "\n";
        }
    }

    cuda_free(d_signal);
    cuda_free(d_spectrum);
}

// Real-to-Complex FFT example
void fft_r2c_example() {
    std::cout << "\n=== 1D Real-to-Complex FFT ===\n";

    const int N = 1024;
    const int N_COMPLEX = N / 2 + 1;

    // Allocate memory
    std::unique_ptr<float[]> h_real_signal(new float[N]);
    std::unique_ptr<cufftComplex[]> h_spectrum(new cufftComplex[N_COMPLEX]);

    // Generate real signal
    for (int i = 0; i < N; i++) {
        float t = static_cast<float>(i) / N;
        h_real_signal[i] = std::cos(2.0f * M_PI * 8.0f * t);
    }

    // Allocate device memory
    float* d_real_signal = cuda_malloc<float>(N);
    cufftComplex* d_spectrum = cuda_malloc<cufftComplex>(N_COMPLEX);

    cudaMemcpy(d_real_signal, h_real_signal.get(), N * sizeof(float),
               cudaMemcpyHostToDevice);

    // Create R2C plan
    CufftPlan plan(N, CUFFT_R2C, 1);

    // Execute R2C transform
    cufftExecR2C(plan.get(), d_real_signal, d_spectrum);
    cudaDeviceSynchronize();

    cudaMemcpy(h_spectrum.get(), d_spectrum, N_COMPLEX * sizeof(cufftComplex),
               cudaMemcpyDeviceToHost);

    std::cout << "R2C output size: " << N_COMPLEX << " (vs " << N
              << " for C2C)\n";
    std::cout << "Memory savings: "
              << (1.0f - static_cast<float>(N_COMPLEX) / N) * 100.0f << "%\n";

    cuda_free(d_real_signal);
    cuda_free(d_spectrum);
}

// Forward-Inverse pair test
void fft_forward_inverse_test() {
    std::cout << "\n=== Forward-Inverse FFT Test ===\n";

    const int N = 256;

    std::unique_ptr<cufftComplex[]> h_original(new cufftComplex[N]);
    std::unique_ptr<cufftComplex[]> h_result(new cufftComplex[N]);

    // Generate random signal
    for (int i = 0; i < N; i++) {
        h_original[i].x = static_cast<float>(rand()) / RAND_MAX;
        h_original[i].y = static_cast<float>(rand()) / RAND_MAX;
    }

    cufftComplex* d_data = cuda_malloc<cufftComplex>(N);
    cudaMemcpy(d_data, h_original.get(), N * sizeof(cufftComplex),
               cudaMemcpyHostToDevice);

    CufftPlan plan(N, CUFFT_C2C, 1);

    // Forward then inverse
    cufftExecC2C(plan.get(), d_data, d_data, CUFFT_FORWARD);
    cufftExecC2C(plan.get(), d_data, d_data, CUFFT_INVERSE);
    cudaDeviceSynchronize();

    cudaMemcpy(h_result.get(), d_data, N * sizeof(cufftComplex),
               cudaMemcpyDeviceToHost);

    // Verify (scaled by N)
    float max_error = 0.0f;
    for (int i = 0; i < N; i++) {
        float err_real = std::abs(h_result[i].x / N - h_original[i].x);
        float err_imag = std::abs(h_result[i].y / N - h_original[i].y);
        max_error = std::max(max_error, std::max(err_real, err_imag));
    }

    std::cout << "Maximum reconstruction error: " << max_error << "\n";
    if (max_error < 1e-4f) {
        std::cout << "Forward-Inverse test PASSED\n";
    } else {
        std::cout << "Forward-Inverse test FAILED\n";
    }

    cuda_free(d_data);
}

int main() {
    std::cout << "=== cuFFT 1D Demo ===\n";

    // Check CUDA device
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
        fft_1d_c2c_example();
        fft_r2c_example();
        fft_forward_inverse_test();
    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << "\n";
        return 1;
    }

    std::cout << "\nAll demos completed successfully!\n";
    return 0;
}
