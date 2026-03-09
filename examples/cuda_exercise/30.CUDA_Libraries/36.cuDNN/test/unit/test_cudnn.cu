#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include <cudnn.h>

class CudnnTest : public GpuTest {};

TEST_F(CudnnTest, HandleCreation) {
    cudnnHandle_t handle;
    ASSERT_EQ(cudnnCreate(&handle), CUDNN_STATUS_SUCCESS);
    ASSERT_EQ(cudnnDestroy(handle), CUDNN_STATUS_SUCCESS);
}

TEST_F(CudnnTest, VersionCheck) {
    size_t version = cudnnGetVersion();
    EXPECT_GT(version, 0);
}
