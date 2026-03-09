// test_cufft_2d.cu - 2D FFT tests
#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include <cufft.h>
#include "cuda_utils.h"
#include <cmath>
#include <memory>

class Cufft2DTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }
};

TEST_F(Cufft2DTest, Basic2DTransform) {
    const int WIDTH = 64;
    const int HEIGHT = 64;
    const int SIZE = WIDTH * HEIGHT;

    std::unique_ptr<cufftComplex[]> h_image(new cufftComplex[SIZE]);
    std::unique_ptr<cufftComplex[]> h_spectrum(new cufftComplex[SIZE]);

    // Create impulse at center
    for (int i = 0; i < SIZE; i++) {
        h_image[i].x = 0.0f;
        h_image[i].y = 0.0f;
    }
    h_image[HEIGHT/2 * WIDTH + WIDTH/2].x = 1.0f;

    cufftComplex* d_image = cuda_malloc<cufftComplex>(SIZE);
    cufftComplex* d_spectrum = cuda_malloc<cufftComplex>(SIZE);

    cudaMemcpy(d_image, h_image.get(), SIZE * sizeof(cufftComplex),
               cudaMemcpyHostToDevice);

    cufftHandle plan;
    ASSERT_EQ(cufftPlan2d(&plan, HEIGHT, WIDTH, CUFFT_C2C), CUFFT_SUCCESS);
    ASSERT_EQ(cufftExecC2C(plan, d_image, d_spectrum, CUFFT_FORWARD),
              CUFFT_SUCCESS);
    cudaDeviceSynchronize();

    cudaMemcpy(h_spectrum.get(), d_spectrum, SIZE * sizeof(cufftComplex),
               cudaMemcpyDeviceToHost);

    // Check DC component
    float dc_real = h_spectrum[0].x;
    EXPECT_NEAR(dc_real, 1.0f, 1e-5f);

    cufftDestroy(plan);
    cuda_free(d_image);
    cuda_free(d_spectrum);
}

TEST_F(Cufft2DTest, ForwardInverse2D) {
    const int WIDTH = 128;
    const int HEIGHT = 128;
    const int SIZE = WIDTH * HEIGHT;

    std::unique_ptr<cufftComplex[]> h_original(new cufftComplex[SIZE]);
    std::unique_ptr<cufftComplex[]> h_result(new cufftComplex[SIZE]);

    // Random image
    for (int i = 0; i < SIZE; i++) {
        h_original[i].x = static_cast<float>(rand()) / RAND_MAX;
        h_original[i].y = static_cast<float>(rand()) / RAND_MAX;
    }

    cufftComplex* d_data = cuda_malloc<cufftComplex>(SIZE);
    cudaMemcpy(d_data, h_original.get(), SIZE * sizeof(cufftComplex),
               cudaMemcpyHostToDevice);

    cufftHandle plan;
    ASSERT_EQ(cufftPlan2d(&plan, HEIGHT, WIDTH, CUFFT_C2C), CUFFT_SUCCESS);

    // Forward then inverse
    ASSERT_EQ(cufftExecC2C(plan, d_data, d_data, CUFFT_FORWARD), CUFFT_SUCCESS);
    ASSERT_EQ(cufftExecC2C(plan, d_data, d_data, CUFFT_INVERSE), CUFFT_SUCCESS);
    cudaDeviceSynchronize();

    cudaMemcpy(h_result.get(), d_data, SIZE * sizeof(cufftComplex),
               cudaMemcpyDeviceToHost);

    // Verify (scaled by SIZE)
    for (int i = 0; i < SIZE; i++) {
        EXPECT_NEAR(h_result[i].x / SIZE, h_original[i].x, 1e-3f);
        EXPECT_NEAR(h_result[i].y / SIZE, h_original[i].y, 1e-3f);
    }

    cufftDestroy(plan);
    cuda_free(d_data);
}

TEST_F(Cufft2DTest, CheckerboardFrequency) {
    const int WIDTH = 64;
    const int HEIGHT = 64;
    const int SIZE = WIDTH * HEIGHT;
    const int SQUARE_SIZE = 8;

    std::unique_ptr<cufftComplex[]> h_image(new cufftComplex[SIZE]);
    std::unique_ptr<cufftComplex[]> h_spectrum(new cufftComplex[SIZE]);

    // Create checkerboard pattern
    for (int y = 0; y < HEIGHT; y++) {
        for (int x = 0; x < WIDTH; x++) {
            int idx = y * WIDTH + x;
            bool isWhite = ((x / SQUARE_SIZE) + (y / SQUARE_SIZE)) % 2 == 0;
            h_image[idx].x = isWhite ? 1.0f : 0.0f;
            h_image[idx].y = 0.0f;
        }
    }

    cufftComplex* d_image = cuda_malloc<cufftComplex>(SIZE);
    cufftComplex* d_spectrum = cuda_malloc<cufftComplex>(SIZE);

    cudaMemcpy(d_image, h_image.get(), SIZE * sizeof(cufftComplex),
               cudaMemcpyHostToDevice);

    cufftHandle plan;
    ASSERT_EQ(cufftPlan2d(&plan, HEIGHT, WIDTH, CUFFT_C2C), CUFFT_SUCCESS);
    ASSERT_EQ(cufftExecC2C(plan, d_image, d_spectrum, CUFFT_FORWARD),
              CUFFT_SUCCESS);
    cudaDeviceSynchronize();

    cudaMemcpy(h_spectrum.get(), d_spectrum, SIZE * sizeof(cufftComplex),
               cudaMemcpyDeviceToHost);

    // DC component should be 0.5 (average of checkerboard)
    EXPECT_NEAR(h_spectrum[0].x / SIZE, 0.5f, 1e-2f);

    // Should have energy at fundamental frequency
    int freq_bin = WIDTH / SQUARE_SIZE;
    int idx1 = 0 * WIDTH + freq_bin;
    int idx2 = freq_bin * WIDTH + 0;

    float mag1 = std::sqrt(h_spectrum[idx1].x * h_spectrum[idx1].x +
                          h_spectrum[idx1].y * h_spectrum[idx1].y);
    float mag2 = std::sqrt(h_spectrum[idx2].x * h_spectrum[idx2].x +
                          h_spectrum[idx2].y * h_spectrum[idx2].y);

    EXPECT_GT(mag1, 100.0f) << "Expected energy at horizontal frequency";
    EXPECT_GT(mag2, 100.0f) << "Expected energy at vertical frequency";

    cufftDestroy(plan);
    cuda_free(d_image);
    cuda_free(d_spectrum);
}

TEST_F(Cufft2DTest, Batched2DFFT) {
    const int WIDTH = 32;
    const int HEIGHT = 32;
    const int BATCH = 5;
    const int SIZE_2D = WIDTH * HEIGHT;
    const int TOTAL_SIZE = SIZE_2D * BATCH;

    std::unique_ptr<cufftComplex[]> h_images(new cufftComplex[TOTAL_SIZE]);
    std::unique_ptr<cufftComplex[]> h_spectra(new cufftComplex[TOTAL_SIZE]);

    // Create batch of impulses
    for (int b = 0; b < BATCH; b++) {
        for (int i = 0; i < SIZE_2D; i++) {
            int idx = b * SIZE_2D + i;
            h_images[idx].x = (i == 0) ? 1.0f : 0.0f;
            h_images[idx].y = 0.0f;
        }
    }

    cufftComplex* d_images = cuda_malloc<cufftComplex>(TOTAL_SIZE);
    cufftComplex* d_spectra = cuda_malloc<cufftComplex>(TOTAL_SIZE);

    cudaMemcpy(d_images, h_images.get(), TOTAL_SIZE * sizeof(cufftComplex),
               cudaMemcpyHostToDevice);

    // Create batched 2D plan
    cufftHandle plan;
    int n[2] = {HEIGHT, WIDTH};
    ASSERT_EQ(cufftPlanMany(&plan, 2, n,
                            nullptr, 1, SIZE_2D,
                            nullptr, 1, SIZE_2D,
                            CUFFT_C2C, BATCH), CUFFT_SUCCESS);

    ASSERT_EQ(cufftExecC2C(plan, d_images, d_spectra, CUFFT_FORWARD),
              CUFFT_SUCCESS);
    cudaDeviceSynchronize();

    cudaMemcpy(h_spectra.get(), d_spectra, TOTAL_SIZE * sizeof(cufftComplex),
               cudaMemcpyDeviceToHost);

    // Each batch should have all ones (FFT of impulse)
    for (int b = 0; b < BATCH; b++) {
        for (int i = 0; i < SIZE_2D; i++) {
            int idx = b * SIZE_2D + i;
            EXPECT_NEAR(h_spectra[idx].x, 1.0f, 1e-4f);
            EXPECT_NEAR(h_spectra[idx].y, 0.0f, 1e-4f);
        }
    }

    cufftDestroy(plan);
    cuda_free(d_images);
    cuda_free(d_spectra);
}

TEST_F(Cufft2DTest, Real2DTransform) {
    const int WIDTH = 128;
    const int HEIGHT = 64;
    const int SIZE = WIDTH * HEIGHT;
    const int N_COMPLEX = WIDTH * (HEIGHT / 2 + 1);

    std::unique_ptr<float[]> h_real_image(new float[SIZE]);
    std::unique_ptr<cufftComplex[]> h_spectrum(new cufftComplex[N_COMPLEX]);

    // Generate real image
    for (int y = 0; y < HEIGHT; y++) {
        for (int x = 0; x < WIDTH; x++) {
            int idx = y * WIDTH + x;
            h_real_image[idx] = std::sin(2.0f * M_PI * x / WIDTH);
        }
    }

    float* d_real_image = cuda_malloc<float>(SIZE);
    cufftComplex* d_spectrum = cuda_malloc<cufftComplex>(N_COMPLEX);

    cudaMemcpy(d_real_image, h_real_image.get(), SIZE * sizeof(float),
               cudaMemcpyHostToDevice);

    cufftHandle plan;
    ASSERT_EQ(cufftPlan2d(&plan, HEIGHT, WIDTH, CUFFT_R2C), CUFFT_SUCCESS);
    ASSERT_EQ(cufftExecR2C(plan, d_real_image, d_spectrum), CUFFT_SUCCESS);
    cudaDeviceSynchronize();

    cudaMemcpy(h_spectrum.get(), d_spectrum, N_COMPLEX * sizeof(cufftComplex),
               cudaMemcpyDeviceToHost);

    // Verify DC component is near zero (sine wave average)
    EXPECT_NEAR(h_spectrum[0].x, 0.0f, 1.0f);

    cufftDestroy(plan);
    cuda_free(d_real_image);
    cuda_free(d_spectrum);
}
