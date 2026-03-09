/**
 * @file test_checkpoint.cpp
 * @brief Unit tests for binary checkpoint save/load
 *
 * Tests the checkpoint serialization format by verifying:
 * - Save/load roundtrip preserves all parameter values
 * - Header validation detects invalid files
 * - Parameter count query works without loading data
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/checkpoint.h"
#include "cuda_utils.h"
#include <vector>
#include <cstdio>
#include <cstring>
#include <cstdlib>

namespace llm {

class CheckpointTest : public GpuTest {
protected:
    std::string temp_path;

    void SetUp() override {
        GpuTest::SetUp();
        // Create a temporary file path
        temp_path = "/tmp/test_checkpoint_XXXXXX";
        int fd = mkstemp(&temp_path[0]);
        if (fd >= 0) close(fd);
    }

    void TearDown() override {
        // Clean up temp file
        std::remove(temp_path.c_str());
        GpuTest::TearDown();
    }
};

TEST_F(CheckpointTest, SaveLoadRoundtrip) {
    // Create test tensor metadata
    const int num_elements = 256;
    std::vector<TensorMeta> tensors_in(1);
    tensors_in[0].name = "test_weights";
    tensors_in[0].shape = {16, 16};
    tensors_in[0].offset = 0;
    tensors_in[0].num_elements = num_elements;

    // Create test data on host
    std::vector<float> h_data(num_elements);
    for (int i = 0; i < num_elements; i++) {
        h_data[i] = 0.01f * i - 1.28f;
    }

    // Copy to device
    float* d_data = nullptr;
    CHECK_CUDA(cudaMalloc(&d_data, num_elements * sizeof(float)));
    CHECK_CUDA(cudaMemcpy(d_data, h_data.data(), num_elements * sizeof(float),
                          cudaMemcpyHostToDevice));

    // Save checkpoint
    ASSERT_TRUE(save_checkpoint(temp_path, d_data, tensors_in));

    // Load checkpoint into a new buffer
    float* d_loaded = nullptr;
    CHECK_CUDA(cudaMalloc(&d_loaded, num_elements * sizeof(float)));

    std::vector<TensorMeta> tensors_out;
    ASSERT_TRUE(load_checkpoint(temp_path, d_loaded, tensors_out));

    // Verify metadata
    ASSERT_EQ(tensors_out.size(), 1u);
    EXPECT_EQ(tensors_out[0].name, "test_weights");
    EXPECT_EQ(tensors_out[0].num_elements, num_elements);
    ASSERT_EQ(tensors_out[0].shape.size(), 2u);
    EXPECT_EQ(tensors_out[0].shape[0], 16);
    EXPECT_EQ(tensors_out[0].shape[1], 16);

    // Verify data matches
    std::vector<float> h_loaded(num_elements);
    CHECK_CUDA(cudaMemcpy(h_loaded.data(), d_loaded, num_elements * sizeof(float),
                          cudaMemcpyDeviceToHost));

    for (int i = 0; i < num_elements; i++) {
        EXPECT_FLOAT_EQ(h_loaded[i], h_data[i])
            << "Mismatch at index " << i;
    }

    cudaFree(d_data);
    cudaFree(d_loaded);
}

TEST_F(CheckpointTest, MultipleTensors) {
    // Save two tensors
    std::vector<TensorMeta> tensors_in(2);
    tensors_in[0].name = "embedding";
    tensors_in[0].shape = {10, 8};
    tensors_in[0].offset = 0;
    tensors_in[0].num_elements = 80;
    tensors_in[1].name = "linear";
    tensors_in[1].shape = {8, 4};
    tensors_in[1].offset = 80 * sizeof(float);
    tensors_in[1].num_elements = 32;

    int64_t total = 80 + 32;
    std::vector<float> h_data(total);
    for (int64_t i = 0; i < total; i++) {
        h_data[i] = static_cast<float>(i);
    }

    float* d_data = nullptr;
    CHECK_CUDA(cudaMalloc(&d_data, total * sizeof(float)));
    CHECK_CUDA(cudaMemcpy(d_data, h_data.data(), total * sizeof(float),
                          cudaMemcpyHostToDevice));

    ASSERT_TRUE(save_checkpoint(temp_path, d_data, tensors_in));

    // Verify param count without loading
    int64_t count = get_checkpoint_param_count(temp_path);
    EXPECT_EQ(count, total);

    // Load and verify
    float* d_loaded = nullptr;
    CHECK_CUDA(cudaMalloc(&d_loaded, total * sizeof(float)));

    std::vector<TensorMeta> tensors_out;
    ASSERT_TRUE(load_checkpoint(temp_path, d_loaded, tensors_out));
    ASSERT_EQ(tensors_out.size(), 2u);
    EXPECT_EQ(tensors_out[0].name, "embedding");
    EXPECT_EQ(tensors_out[1].name, "linear");

    std::vector<float> h_loaded(total);
    CHECK_CUDA(cudaMemcpy(h_loaded.data(), d_loaded, total * sizeof(float),
                          cudaMemcpyDeviceToHost));

    for (int64_t i = 0; i < total; i++) {
        EXPECT_FLOAT_EQ(h_loaded[i], h_data[i]);
    }

    cudaFree(d_data);
    cudaFree(d_loaded);
}

TEST_F(CheckpointTest, InvalidFileReturnsError) {
    // Try loading from a non-existent file
    float* d_data = nullptr;
    CHECK_CUDA(cudaMalloc(&d_data, 4));
    std::vector<TensorMeta> tensors;
    EXPECT_FALSE(load_checkpoint("/tmp/nonexistent_checkpoint_file.bin", d_data, tensors));
    cudaFree(d_data);
}

TEST_F(CheckpointTest, GetParamCountFromInvalidFile) {
    int64_t count = get_checkpoint_param_count("/tmp/nonexistent_checkpoint_file.bin");
    EXPECT_EQ(count, -1);
}

} // namespace llm
