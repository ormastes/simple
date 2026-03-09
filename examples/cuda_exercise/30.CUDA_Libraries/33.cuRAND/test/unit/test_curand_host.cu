#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include <curand.h>
#include "cuda_utils.h"
#include <memory>

class CurandHostTest : public GpuTest {};

TEST_F(CurandHostTest, UniformRange) {
    const int N = 10000;
    curandGenerator_t gen;
    ASSERT_EQ(curandCreateGenerator(&gen, CURAND_RNG_PSEUDO_DEFAULT), CURAND_STATUS_SUCCESS);
    curandSetPseudoRandomGeneratorSeed(gen, 1234ULL);

    float* d_random = cuda_malloc<float>(N);
    ASSERT_EQ(curandGenerateUniform(gen, d_random, N), CURAND_STATUS_SUCCESS);

    std::unique_ptr<float[]> h_random(new float[N]);
    cudaMemcpy(h_random.get(), d_random, N * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < N; i++) {
        EXPECT_GE(h_random[i], 0.0f);
        EXPECT_LT(h_random[i], 1.0f);
    }

    curandDestroyGenerator(gen);
    cuda_free(d_random);
}

TEST_F(CurandHostTest, NormalMean) {
    const int N = 100000;
    curandGenerator_t gen;
    curandCreateGenerator(&gen, CURAND_RNG_PSEUDO_DEFAULT);
    curandSetPseudoRandomGeneratorSeed(gen, 42ULL);

    float* d_random = cuda_malloc<float>(N);
    curandGenerateNormal(gen, d_random, N, 0.0f, 1.0f);

    std::unique_ptr<float[]> h_random(new float[N]);
    cudaMemcpy(h_random.get(), d_random, N * sizeof(float), cudaMemcpyDeviceToHost);

    double mean = 0.0;
    for (int i = 0; i < N; i++) mean += h_random[i];
    mean /= N;

    EXPECT_NEAR(mean, 0.0, 0.02);

    curandDestroyGenerator(gen);
    cuda_free(d_random);
}
