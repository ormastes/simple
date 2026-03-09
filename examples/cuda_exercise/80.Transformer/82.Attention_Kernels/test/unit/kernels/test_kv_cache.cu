/**
 * @file test_kv_cache.cu
 * @brief Unit tests for KV cache management kernels
 *
 * Validates that KV cache append and read operations produce correct results,
 * including sequential appends and multi-head layouts.
 */

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include <vector>
#include <cmath>

namespace transformer {
extern void launch_kv_cache_append(float* cache, const float* new_kv,
                                    int cache_offset, int num_new,
                                    int num_heads, int head_dim, cudaStream_t stream);
extern void launch_kv_cache_read(float* output, const float* cache,
                                  int seq_len, int num_heads, int head_dim, cudaStream_t stream);
}

/**
 * @brief Test fixture for KV cache tests
 */
class KVCacheTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }

    void TearDown() override {
        GpuTest::TearDown();
    }
};

/**
 * @brief Append then read: verify cache contents match appended data
 */
TEST_F(KVCacheTest, AppendThenRead_MatchesInput) {
    const int max_seq = 16;
    const int num_heads = 2;
    const int head_dim = 4;
    const int num_new = 3;
    const int cache_size = max_seq * num_heads * head_dim;
    const int new_size = num_new * num_heads * head_dim;

    // Prepare new KV data
    std::vector<float> h_new_kv(new_size);
    for (int i = 0; i < new_size; i++) {
        h_new_kv[i] = static_cast<float>(i + 1) * 0.5f;
    }

    float* d_cache = cuda_calloc<float>(cache_size);
    float* d_new_kv = cuda_malloc<float>(new_size);
    float* d_output = cuda_malloc<float>(new_size);
    CHECK_CUDA(cudaMemcpy(d_new_kv, h_new_kv.data(), new_size * sizeof(float), cudaMemcpyHostToDevice));

    // Append at offset 0
    transformer::launch_kv_cache_append(d_cache, d_new_kv, 0, num_new,
                                         num_heads, head_dim, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    // Read back the first num_new entries
    transformer::launch_kv_cache_read(d_output, d_cache, num_new, num_heads, head_dim, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(new_size);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, new_size * sizeof(float), cudaMemcpyDeviceToHost));

    for (int i = 0; i < new_size; i++) {
        EXPECT_FLOAT_EQ(h_output[i], h_new_kv[i])
            << "Mismatch at index " << i;
    }

    cuda_free(d_cache);
    cuda_free(d_new_kv);
    cuda_free(d_output);
}

/**
 * @brief Sequential appends should accumulate correctly in the cache
 */
TEST_F(KVCacheTest, SequentialAppends_Accumulate) {
    const int max_seq = 16;
    const int num_heads = 2;
    const int head_dim = 4;
    const int stride = num_heads * head_dim;
    const int cache_size = max_seq * stride;

    // First batch: 2 tokens
    const int num_new1 = 2;
    const int size1 = num_new1 * stride;
    std::vector<float> h_batch1(size1);
    for (int i = 0; i < size1; i++) {
        h_batch1[i] = static_cast<float>(i + 1);
    }

    // Second batch: 3 tokens
    const int num_new2 = 3;
    const int size2 = num_new2 * stride;
    std::vector<float> h_batch2(size2);
    for (int i = 0; i < size2; i++) {
        h_batch2[i] = static_cast<float>(i + 100);
    }

    float* d_cache = cuda_calloc<float>(cache_size);
    float* d_batch1 = cuda_malloc<float>(size1);
    float* d_batch2 = cuda_malloc<float>(size2);
    CHECK_CUDA(cudaMemcpy(d_batch1, h_batch1.data(), size1 * sizeof(float), cudaMemcpyHostToDevice));
    CHECK_CUDA(cudaMemcpy(d_batch2, h_batch2.data(), size2 * sizeof(float), cudaMemcpyHostToDevice));

    // Append first batch at offset 0
    transformer::launch_kv_cache_append(d_cache, d_batch1, 0, num_new1,
                                         num_heads, head_dim, 0);
    // Append second batch at offset 2
    transformer::launch_kv_cache_append(d_cache, d_batch2, num_new1, num_new2,
                                         num_heads, head_dim, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    // Read all 5 entries
    int total_seq = num_new1 + num_new2;
    int total_size = total_seq * stride;
    float* d_output = cuda_malloc<float>(total_size);
    transformer::launch_kv_cache_read(d_output, d_cache, total_seq, num_heads, head_dim, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_output(total_size);
    CHECK_CUDA(cudaMemcpy(h_output.data(), d_output, total_size * sizeof(float), cudaMemcpyDeviceToHost));

    // First num_new1 entries should match batch1
    for (int i = 0; i < size1; i++) {
        EXPECT_FLOAT_EQ(h_output[i], h_batch1[i])
            << "Batch1 mismatch at index " << i;
    }

    // Next num_new2 entries should match batch2
    for (int i = 0; i < size2; i++) {
        EXPECT_FLOAT_EQ(h_output[size1 + i], h_batch2[i])
            << "Batch2 mismatch at index " << i;
    }

    cuda_free(d_cache);
    cuda_free(d_batch1);
    cuda_free(d_batch2);
    cuda_free(d_output);
}

/**
 * @brief Verify cache layout: [seq_len, num_heads, head_dim] indexing
 */
TEST_F(KVCacheTest, LayoutVerification) {
    const int max_seq = 8;
    const int num_heads = 3;
    const int head_dim = 4;
    const int stride = num_heads * head_dim;
    const int cache_size = max_seq * stride;

    // Create data with a known pattern: value = t * 1000 + h * 100 + d
    const int num_new = 2;
    const int new_size = num_new * stride;
    std::vector<float> h_new(new_size);
    for (int t = 0; t < num_new; t++) {
        for (int h = 0; h < num_heads; h++) {
            for (int d = 0; d < head_dim; d++) {
                h_new[t * stride + h * head_dim + d] =
                    static_cast<float>(t * 1000 + h * 100 + d);
            }
        }
    }

    float* d_cache = cuda_calloc<float>(cache_size);
    float* d_new = cuda_malloc<float>(new_size);
    CHECK_CUDA(cudaMemcpy(d_new, h_new.data(), new_size * sizeof(float), cudaMemcpyHostToDevice));

    transformer::launch_kv_cache_append(d_cache, d_new, 0, num_new,
                                         num_heads, head_dim, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    // Read raw cache and verify layout
    std::vector<float> h_cache(cache_size);
    CHECK_CUDA(cudaMemcpy(h_cache.data(), d_cache, cache_size * sizeof(float), cudaMemcpyDeviceToHost));

    for (int t = 0; t < num_new; t++) {
        for (int h = 0; h < num_heads; h++) {
            for (int d = 0; d < head_dim; d++) {
                float expected = static_cast<float>(t * 1000 + h * 100 + d);
                int cache_idx = t * stride + h * head_dim + d;
                EXPECT_FLOAT_EQ(h_cache[cache_idx], expected)
                    << "Layout mismatch at t=" << t << ", h=" << h << ", d=" << d;
            }
        }
    }

    // Verify remaining cache entries are still zero
    for (int t = num_new; t < max_seq; t++) {
        for (int i = 0; i < stride; i++) {
            EXPECT_FLOAT_EQ(h_cache[t * stride + i], 0.0f)
                << "Untouched cache entry should be zero at t=" << t << ", i=" << i;
        }
    }

    cuda_free(d_cache);
    cuda_free(d_new);
}

/**
 * @brief Append with non-zero offset should write to correct positions
 */
TEST_F(KVCacheTest, AppendWithOffset) {
    const int max_seq = 8;
    const int num_heads = 1;
    const int head_dim = 4;
    const int stride = num_heads * head_dim;
    const int cache_size = max_seq * stride;

    const int offset = 3;
    const int num_new = 2;
    const int new_size = num_new * stride;

    std::vector<float> h_new(new_size);
    for (int i = 0; i < new_size; i++) {
        h_new[i] = static_cast<float>(i + 42);
    }

    float* d_cache = cuda_calloc<float>(cache_size);
    float* d_new = cuda_malloc<float>(new_size);
    CHECK_CUDA(cudaMemcpy(d_new, h_new.data(), new_size * sizeof(float), cudaMemcpyHostToDevice));

    transformer::launch_kv_cache_append(d_cache, d_new, offset, num_new,
                                         num_heads, head_dim, 0);
    CHECK_CUDA(cudaDeviceSynchronize());

    std::vector<float> h_cache(cache_size);
    CHECK_CUDA(cudaMemcpy(h_cache.data(), d_cache, cache_size * sizeof(float), cudaMemcpyDeviceToHost));

    // Entries before offset should be zero
    for (int i = 0; i < offset * stride; i++) {
        EXPECT_FLOAT_EQ(h_cache[i], 0.0f)
            << "Entry before offset should be zero at index " << i;
    }

    // Entries at offset should match new_kv
    for (int i = 0; i < new_size; i++) {
        EXPECT_FLOAT_EQ(h_cache[offset * stride + i], h_new[i])
            << "Offset append mismatch at index " << i;
    }

    // Entries after should be zero
    for (int i = (offset + num_new) * stride; i < cache_size; i++) {
        EXPECT_FLOAT_EQ(h_cache[i], 0.0f)
            << "Entry after append should be zero at index " << i;
    }

    cuda_free(d_cache);
    cuda_free(d_new);
}
