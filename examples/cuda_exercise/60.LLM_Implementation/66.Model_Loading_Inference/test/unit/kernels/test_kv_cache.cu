/**
 * @file test_kv_cache.cu
 * @brief Unit tests for KV cache CUDA kernels
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "common/inference_engine.h"
#include "common/kv_cache_ops.h"
#include "cuda_utils.h"
#include <vector>

namespace llm {

class KVCacheKernelTest : public GpuTest {
protected:
    KVCache cache;
    int num_layers = 2;
    int max_seq_len = 16;
    int num_heads = 4;
    int head_dim = 8;
    int d; // num_heads * head_dim

    void SetUp() override {
        GpuTest::SetUp();
        d = num_heads * head_dim;
        cache = allocate_kv_cache(num_layers, max_seq_len, num_heads, head_dim);
    }

    void TearDown() override {
        free_kv_cache(cache);
        GpuTest::TearDown();
    }

    int layer_pos_offset(int layer, int position) const {
        return layer * max_seq_len * d + position * d;
    }
};

TEST_F(KVCacheKernelTest, AppendSingleToken) {
    std::vector<float> h_keys(d), h_values(d);
    for (int i = 0; i < d; i++) {
        h_keys[i] = static_cast<float>(i);
        h_values[i] = static_cast<float>(i + 100);
    }

    float* d_keys = nullptr;
    float* d_values = nullptr;
    CHECK_CUDA(cudaMalloc(&d_keys, d * sizeof(float)));
    CHECK_CUDA(cudaMalloc(&d_values, d * sizeof(float)));
    CHECK_CUDA(cudaMemcpy(d_keys, h_keys.data(), d * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_values, h_values.data(), d * sizeof(float), cudaMemcpyHostToDevice));

    // Append 1 token at layer 0, then layer 1 (last layer updates counter)
    kv_cache_append(cache, d_keys, d_values, 0, 1);
    EXPECT_EQ(cache.current_len, 0);
    kv_cache_append(cache, d_keys, d_values, 1, 1);
    EXPECT_EQ(cache.current_len, 1);
    CHECK_CUDA(cudaDeviceSynchronize());

    // Read back from layer 0 key cache
    std::vector<float> h_readback(d);
    CHECK_CUDA(cudaMemcpy(h_readback.data(),
                          cache.d_key_cache + layer_pos_offset(0, 0),
                          d * sizeof(float), cudaMemcpyDeviceToHost));
    for (int i = 0; i < d; i++) {
        EXPECT_FLOAT_EQ(h_readback[i], h_keys[i]) << "Key mismatch at dim " << i;
    }

    // Read back from layer 0 value cache
    CHECK_CUDA(cudaMemcpy(h_readback.data(),
                          cache.d_value_cache + layer_pos_offset(0, 0),
                          d * sizeof(float), cudaMemcpyDeviceToHost));
    for (int i = 0; i < d; i++) {
        EXPECT_FLOAT_EQ(h_readback[i], h_values[i]) << "Value mismatch at dim " << i;
    }

    cudaFree(d_keys);
    cudaFree(d_values);
}

TEST_F(KVCacheKernelTest, AppendMultipleTokens) {
    int num_tokens = 3;
    std::vector<float> h_keys(num_tokens * d);
    for (int t = 0; t < num_tokens; t++)
        for (int i = 0; i < d; i++)
            h_keys[t * d + i] = static_cast<float>(t * 10 + i);

    float* d_keys = nullptr;
    CHECK_CUDA(cudaMalloc(&d_keys, num_tokens * d * sizeof(float)));
    CHECK_CUDA(cudaMemcpy(d_keys, h_keys.data(), num_tokens * d * sizeof(float),
                          cudaMemcpyHostToDevice));

    // Append all tokens at once for both layers
    for (int l = 0; l < num_layers; l++) {
        kv_cache_append(cache, d_keys, d_keys, l, num_tokens);
    }
    EXPECT_EQ(cache.current_len, num_tokens);
    CHECK_CUDA(cudaDeviceSynchronize());

    // Verify token 2 in layer 0 key cache
    std::vector<float> h_readback(d);
    CHECK_CUDA(cudaMemcpy(h_readback.data(),
                          cache.d_key_cache + layer_pos_offset(0, 2),
                          d * sizeof(float), cudaMemcpyDeviceToHost));
    for (int i = 0; i < d; i++) {
        EXPECT_FLOAT_EQ(h_readback[i], h_keys[2 * d + i])
            << "Key token 2 mismatch at dim " << i;
    }

    cudaFree(d_keys);
}

TEST_F(KVCacheKernelTest, RotateShiftsCorrectly) {
    int num_tokens = 4;
    std::vector<float> h_keys(num_tokens * d);
    for (int t = 0; t < num_tokens; t++)
        for (int i = 0; i < d; i++)
            h_keys[t * d + i] = static_cast<float>((t + 1) * 100 + i);

    float* d_keys = nullptr;
    CHECK_CUDA(cudaMalloc(&d_keys, num_tokens * d * sizeof(float)));
    CHECK_CUDA(cudaMemcpy(d_keys, h_keys.data(), num_tokens * d * sizeof(float),
                          cudaMemcpyHostToDevice));

    for (int l = 0; l < num_layers; l++) {
        kv_cache_append(cache, d_keys, d_keys, l, num_tokens);
    }
    EXPECT_EQ(cache.current_len, num_tokens);

    // Rotate by 2: tokens [2,3] become positions [0,1]
    for (int l = 0; l < num_layers; l++) {
        kv_cache_rotate(cache, l, 2);
    }
    EXPECT_EQ(cache.current_len, num_tokens - 2);
    CHECK_CUDA(cudaDeviceSynchronize());

    // Position 0 should now have old position 2's data
    std::vector<float> h_readback(d);
    CHECK_CUDA(cudaMemcpy(h_readback.data(),
                          cache.d_key_cache + layer_pos_offset(0, 0),
                          d * sizeof(float), cudaMemcpyDeviceToHost));
    for (int i = 0; i < d; i++) {
        EXPECT_FLOAT_EQ(h_readback[i], h_keys[2 * d + i])
            << "After rotation, pos 0 should have token 2 data at dim " << i;
    }

    cudaFree(d_keys);
}

TEST_F(KVCacheKernelTest, RotateFullResets) {
    std::vector<float> h_data(d, 1.0f);
    float* d_data = nullptr;
    CHECK_CUDA(cudaMalloc(&d_data, d * sizeof(float)));
    CHECK_CUDA(cudaMemcpy(d_data, h_data.data(), d * sizeof(float), cudaMemcpyHostToDevice));

    for (int l = 0; l < num_layers; l++) {
        kv_cache_append(cache, d_data, d_data, l, 2);
    }
    EXPECT_EQ(cache.current_len, 2);

    // Rotate by more than current length should reset
    kv_cache_rotate(cache, 0, 5);
    EXPECT_EQ(cache.current_len, 0);

    cudaFree(d_data);
}

} // namespace llm
