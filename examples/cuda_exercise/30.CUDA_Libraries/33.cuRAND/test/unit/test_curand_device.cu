#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include <curand_kernel.h>
#include "cuda_utils.h"
#include <memory>

__global__ void gen_kernel(float* out, int n, unsigned long long seed) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        curandState state;
        curand_init(seed, idx, 0, &state);
        out[idx] = curand_uniform(&state);
    }
}

class CurandDeviceTest : public GpuTest {};

TEST_F(CurandDeviceTest, DeviceGeneration) {
    const int N = 1024;
    float* d_output = cuda_malloc<float>(N);

    gen_kernel<<<4, 256>>>(d_output, N, 1234ULL);
    CHECK_KERNEL_LAUNCH();

    std::unique_ptr<float[]> h_output(new float[N]);
    cudaMemcpy(h_output.get(), d_output, N * sizeof(float), cudaMemcpyDeviceToHost);

    for (int i = 0; i < N; i++) {
        EXPECT_GE(h_output[i], 0.0f);
        EXPECT_LT(h_output[i], 1.0f);
    }

    cuda_free(d_output);
}
