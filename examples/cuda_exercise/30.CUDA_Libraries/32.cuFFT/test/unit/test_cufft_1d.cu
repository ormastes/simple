// test_cufft_1d.cu - 1D FFT tests
#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include <cufft.h>
#include "cuda_utils.h"
#include <cmath>
#include <memory>

class Cufft1DTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }

    // Helper: verify FFT of impulse is constant
    void verify_impulse_fft(int N) {
        std::unique_ptr<cufftComplex[]> h_signal(new cufftComplex[N]);
        std::unique_ptr<cufftComplex[]> h_spectrum(new cufftComplex[N]);

        // Impulse at t=0
        for (int i = 0; i < N; i++) {
            h_signal[i].x = (i == 0) ? 1.0f : 0.0f;
            h_signal[i].y = 0.0f;
        }

        cufftComplex* d_signal = cuda_malloc<cufftComplex>(N);
        cufftComplex* d_spectrum = cuda_malloc<cufftComplex>(N);

        cudaMemcpy(d_signal, h_signal.get(), N * sizeof(cufftComplex),
                   cudaMemcpyHostToDevice);

        cufftHandle plan;
        ASSERT_EQ(cufftPlan1d(&plan, N, CUFFT_C2C, 1), CUFFT_SUCCESS);
        ASSERT_EQ(cufftExecC2C(plan, d_signal, d_spectrum, CUFFT_FORWARD),
                  CUFFT_SUCCESS);
        cudaDeviceSynchronize();

        cudaMemcpy(h_spectrum.get(), d_spectrum, N * sizeof(cufftComplex),
                   cudaMemcpyDeviceToHost);

        // FFT of impulse should be all ones
        for (int i = 0; i < N; i++) {
            EXPECT_NEAR(h_spectrum[i].x, 1.0f, 1e-5f)
                << "Real part mismatch at index " << i;
            EXPECT_NEAR(h_spectrum[i].y, 0.0f, 1e-5f)
                << "Imaginary part mismatch at index " << i;
        }

        cufftDestroy(plan);
        cuda_free(d_signal);
        cuda_free(d_spectrum);
    }
};

TEST_F(Cufft1DTest, ImpulseResponse128) {
    verify_impulse_fft(128);
}

TEST_F(Cufft1DTest, ImpulseResponse256) {
    verify_impulse_fft(256);
}

TEST_F(Cufft1DTest, ImpulseResponse1024) {
    verify_impulse_fft(1024);
}

TEST_F(Cufft1DTest, ForwardInversePair) {
    const int N = 256;

    std::unique_ptr<cufftComplex[]> h_original(new cufftComplex[N]);
    std::unique_ptr<cufftComplex[]> h_result(new cufftComplex[N]);

    // Random signal
    for (int i = 0; i < N; i++) {
        h_original[i].x = static_cast<float>(rand()) / RAND_MAX;
        h_original[i].y = static_cast<float>(rand()) / RAND_MAX;
    }

    cufftComplex* d_data = cuda_malloc<cufftComplex>(N);
    cudaMemcpy(d_data, h_original.get(), N * sizeof(cufftComplex),
               cudaMemcpyHostToDevice);

    cufftHandle plan;
    ASSERT_EQ(cufftPlan1d(&plan, N, CUFFT_C2C, 1), CUFFT_SUCCESS);

    // Forward then inverse
    ASSERT_EQ(cufftExecC2C(plan, d_data, d_data, CUFFT_FORWARD), CUFFT_SUCCESS);
    ASSERT_EQ(cufftExecC2C(plan, d_data, d_data, CUFFT_INVERSE), CUFFT_SUCCESS);
    cudaDeviceSynchronize();

    cudaMemcpy(h_result.get(), d_data, N * sizeof(cufftComplex),
               cudaMemcpyDeviceToHost);

    // Should match original (scaled by N)
    for (int i = 0; i < N; i++) {
        EXPECT_NEAR(h_result[i].x / N, h_original[i].x, 1e-4f)
            << "Real part mismatch at index " << i;
        EXPECT_NEAR(h_result[i].y / N, h_original[i].y, 1e-4f)
            << "Imaginary part mismatch at index " << i;
    }

    cufftDestroy(plan);
    cuda_free(d_data);
}

TEST_F(Cufft1DTest, ParsevalsTheorem) {
    const int N = 512;

    std::unique_ptr<cufftComplex[]> h_signal(new cufftComplex[N]);
    std::unique_ptr<cufftComplex[]> h_spectrum(new cufftComplex[N]);

    // Random signal
    float time_energy = 0.0f;
    for (int i = 0; i < N; i++) {
        h_signal[i].x = static_cast<float>(rand()) / RAND_MAX;
        h_signal[i].y = 0.0f;
        time_energy += h_signal[i].x * h_signal[i].x;
    }

    cufftComplex* d_signal = cuda_malloc<cufftComplex>(N);
    cufftComplex* d_spectrum = cuda_malloc<cufftComplex>(N);

    cudaMemcpy(d_signal, h_signal.get(), N * sizeof(cufftComplex),
               cudaMemcpyHostToDevice);

    cufftHandle plan;
    ASSERT_EQ(cufftPlan1d(&plan, N, CUFFT_C2C, 1), CUFFT_SUCCESS);
    ASSERT_EQ(cufftExecC2C(plan, d_signal, d_spectrum, CUFFT_FORWARD),
              CUFFT_SUCCESS);
    cudaDeviceSynchronize();

    cudaMemcpy(h_spectrum.get(), d_spectrum, N * sizeof(cufftComplex),
               cudaMemcpyDeviceToHost);

    // Compute frequency domain energy
    float freq_energy = 0.0f;
    for (int i = 0; i < N; i++) {
        float mag2 = h_spectrum[i].x * h_spectrum[i].x +
                     h_spectrum[i].y * h_spectrum[i].y;
        freq_energy += mag2;
    }
    freq_energy /= N;  // Parseval's theorem scaling

    // Energies should match (Parseval's theorem)
    EXPECT_NEAR(time_energy, freq_energy, 1e-2f);

    cufftDestroy(plan);
    cuda_free(d_signal);
    cuda_free(d_spectrum);
}

TEST_F(Cufft1DTest, RealToComplex) {
    const int N = 1024;
    const int N_COMPLEX = N / 2 + 1;

    std::unique_ptr<float[]> h_real_signal(new float[N]);
    std::unique_ptr<cufftComplex[]> h_spectrum(new cufftComplex[N_COMPLEX]);

    // Generate real signal
    for (int i = 0; i < N; i++) {
        float t = static_cast<float>(i) / N;
        h_real_signal[i] = std::cos(2.0f * M_PI * 8.0f * t);
    }

    float* d_real_signal = cuda_malloc<float>(N);
    cufftComplex* d_spectrum = cuda_malloc<cufftComplex>(N_COMPLEX);

    cudaMemcpy(d_real_signal, h_real_signal.get(), N * sizeof(float),
               cudaMemcpyHostToDevice);

    cufftHandle plan;
    ASSERT_EQ(cufftPlan1d(&plan, N, CUFFT_R2C, 1), CUFFT_SUCCESS);
    ASSERT_EQ(cufftExecR2C(plan, d_real_signal, d_spectrum), CUFFT_SUCCESS);
    cudaDeviceSynchronize();

    cudaMemcpy(h_spectrum.get(), d_spectrum, N_COMPLEX * sizeof(cufftComplex),
               cudaMemcpyDeviceToHost);

    // Check for peak at frequency bin 8
    float max_magnitude = 0.0f;
    int max_idx = 0;
    for (int i = 0; i < N_COMPLEX; i++) {
        float magnitude = std::sqrt(h_spectrum[i].x * h_spectrum[i].x +
                                   h_spectrum[i].y * h_spectrum[i].y);
        if (magnitude > max_magnitude) {
            max_magnitude = magnitude;
            max_idx = i;
        }
    }

    EXPECT_EQ(max_idx, 8) << "Peak should be at frequency bin 8";
    EXPECT_GT(max_magnitude, N / 4.0f) << "Peak magnitude too small";

    cufftDestroy(plan);
    cuda_free(d_real_signal);
    cuda_free(d_spectrum);
}

TEST_F(Cufft1DTest, BatchedFFT) {
    const int N = 128;
    const int BATCH = 10;
    const int TOTAL_SIZE = N * BATCH;

    std::unique_ptr<cufftComplex[]> h_signals(new cufftComplex[TOTAL_SIZE]);
    std::unique_ptr<cufftComplex[]> h_spectra(new cufftComplex[TOTAL_SIZE]);

    // Generate batch of impulses
    for (int b = 0; b < BATCH; b++) {
        for (int i = 0; i < N; i++) {
            int idx = b * N + i;
            h_signals[idx].x = (i == 0) ? 1.0f : 0.0f;
            h_signals[idx].y = 0.0f;
        }
    }

    cufftComplex* d_signals = cuda_malloc<cufftComplex>(TOTAL_SIZE);
    cufftComplex* d_spectra = cuda_malloc<cufftComplex>(TOTAL_SIZE);

    cudaMemcpy(d_signals, h_signals.get(), TOTAL_SIZE * sizeof(cufftComplex),
               cudaMemcpyHostToDevice);

    cufftHandle plan;
    ASSERT_EQ(cufftPlan1d(&plan, N, CUFFT_C2C, BATCH), CUFFT_SUCCESS);
    ASSERT_EQ(cufftExecC2C(plan, d_signals, d_spectra, CUFFT_FORWARD),
              CUFFT_SUCCESS);
    cudaDeviceSynchronize();

    cudaMemcpy(h_spectra.get(), d_spectra, TOTAL_SIZE * sizeof(cufftComplex),
               cudaMemcpyDeviceToHost);

    // Each batch should have all ones
    for (int b = 0; b < BATCH; b++) {
        for (int i = 0; i < N; i++) {
            int idx = b * N + i;
            EXPECT_NEAR(h_spectra[idx].x, 1.0f, 1e-5f);
            EXPECT_NEAR(h_spectra[idx].y, 0.0f, 1e-5f);
        }
    }

    cufftDestroy(plan);
    cuda_free(d_signals);
    cuda_free(d_spectra);
}
