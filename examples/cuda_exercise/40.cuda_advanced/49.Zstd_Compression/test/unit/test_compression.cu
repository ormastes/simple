// test_compression.cu - Tests for compression kernels

#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "cuda_utils.h"
#include "kernels/compression_kernels.cu"

class CompressionTest : public GpuTest {};

TEST_F(CompressionTest, DeltaEncodeWorks) {
    const int N = 1024;
    int* d_input = cuda_malloc<int>(N);
    int* d_encoded = cuda_malloc<int>(N);

    // Create sequential data
    std::vector<int> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = i * 10;
    }
    cuda_memcpy_h2d(d_input, h_input.data(), N);

    // Encode
    delta_encode<<<(N+255)/256, 256>>>(d_input, d_encoded, N);
    CHECK_KERNEL_LAUNCH();

    // Verify encoding produces deltas
    std::vector<int> h_encoded(N);
    cuda_memcpy_d2h(h_encoded.data(), d_encoded, N);

    // First element is original
    EXPECT_EQ(h_encoded[0], 0);

    // Rest are deltas (should all be 10)
    for (int i = 1; i < 10; i++) {
        EXPECT_EQ(h_encoded[i], 10);
    }

    cuda_free(d_input);
    cuda_free(d_encoded);
}

TEST_F(CompressionTest, BitPack4BitWorks) {
    const int N = 1024;
    uint8_t* d_input = cuda_malloc<uint8_t>(N);
    uint8_t* d_packed = cuda_malloc<uint8_t>(N / 2 + 1);
    uint8_t* d_unpacked = cuda_malloc<uint8_t>(N);

    // Create 4-bit values
    std::vector<uint8_t> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = i % 16;  // 4-bit values
    }
    cuda_memcpy_h2d(d_input, h_input.data(), N);

    // Pack
    bit_pack_4bit<<<(N/2+255)/256, 256>>>(d_input, d_packed, N);
    CHECK_KERNEL_LAUNCH();

    // Unpack
    bit_unpack_4bit<<<(N/2+255)/256, 256>>>(d_packed, d_unpacked, N / 2);
    CHECK_KERNEL_LAUNCH();

    // Verify unpacked matches original
    std::vector<uint8_t> h_unpacked(N);
    cuda_memcpy_d2h(h_unpacked.data(), d_unpacked, N);

    for (int i = 0; i < N; i++) {
        EXPECT_EQ(h_unpacked[i], h_input[i]);
    }

    cuda_free(d_input);
    cuda_free(d_packed);
    cuda_free(d_unpacked);
}

TEST_F(CompressionTest, FindPatternsDetectsRepetition) {
    const int N = 1024;
    char* d_input = cuda_malloc<char>(N);
    int* d_matches = cuda_malloc<int>(N);

    // Create data with repeated pattern
    std::vector<char> h_input(N);
    const char pattern[] = "ABCDABCD";
    for (int i = 0; i < N; i++) {
        h_input[i] = pattern[i % 8];
    }
    cuda_memcpy_h2d(d_input, h_input.data(), N);

    // Find patterns
    find_patterns<<<(N+255)/256, 256>>>(d_input, d_matches, N, 256);
    CHECK_KERNEL_LAUNCH();

    // Verify some matches were found
    std::vector<int> h_matches(N);
    cuda_memcpy_d2h(h_matches.data(), d_matches, N);

    int match_count = 0;
    for (int i = 0; i < N; i++) {
        if (h_matches[i] != 0) {
            match_count++;
        }
    }

    EXPECT_GT(match_count, 0);  // Should find some repeated patterns

    cuda_free(d_input);
    cuda_free(d_matches);
}

TEST_F(CompressionTest, CalculateEntropyWorks) {
    const int N = 1024;
    int* d_input = cuda_malloc<int>(N);
    float* d_entropy = cuda_malloc<float>(1);

    // Create data with known distribution
    std::vector<int> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = i % 4;  // 4 symbols with equal probability
    }
    cuda_memcpy_h2d(d_input, h_input.data(), N);

    // Calculate entropy
    calculate_entropy<<<1, 256>>>(d_input, d_entropy, N, 256);
    CHECK_KERNEL_LAUNCH();

    // Verify entropy is reasonable
    float h_entropy;
    cuda_memcpy_d2h(&h_entropy, d_entropy, 1);

    EXPECT_GT(h_entropy, 0.0f);
    EXPECT_LT(h_entropy, 8.0f);  // Max entropy for 256 symbols is 8 bits

    cuda_free(d_input);
    cuda_free(d_entropy);
}

TEST_F(CompressionTest, DeltaEncodingReducesRange) {
    const int N = 1024;
    int* d_input = cuda_malloc<int>(N);
    int* d_encoded = cuda_malloc<int>(N);

    // Create slowly changing sequential data
    std::vector<int> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = 1000 + i;  // Range: 1000 to 2023
    }
    cuda_memcpy_h2d(d_input, h_input.data(), N);

    // Encode
    delta_encode<<<(N+255)/256, 256>>>(d_input, d_encoded, N);
    CHECK_KERNEL_LAUNCH();

    // Verify encoded values are smaller
    std::vector<int> h_encoded(N);
    cuda_memcpy_d2h(h_encoded.data(), d_encoded, N);

    // First element is original, rest are deltas
    EXPECT_EQ(h_encoded[0], 1000);
    for (int i = 1; i < N; i++) {
        EXPECT_EQ(h_encoded[i], 1);  // Delta is always 1
    }

    cuda_free(d_input);
    cuda_free(d_encoded);
}

TEST_F(CompressionTest, BitPackingReducesSize) {
    const int N = 1024;
    uint8_t* d_input = cuda_malloc<uint8_t>(N);
    uint8_t* d_packed = cuda_malloc<uint8_t>(N / 2 + 1);

    // Create 4-bit values
    std::vector<uint8_t> h_input(N);
    for (int i = 0; i < N; i++) {
        h_input[i] = i % 16;
    }
    cuda_memcpy_h2d(d_input, h_input.data(), N);

    // Pack
    bit_pack_4bit<<<(N/2+255)/256, 256>>>(d_input, d_packed, N);
    CHECK_KERNEL_LAUNCH();

    // Verify packed size is half
    std::vector<uint8_t> h_packed(N / 2 + 1);
    cuda_memcpy_d2h(h_packed.data(), d_packed, N / 2 + 1);

    // Each packed byte should contain two 4-bit values
    for (int i = 0; i < 10; i++) {
        uint8_t low = h_packed[i] & 0x0F;
        uint8_t high = (h_packed[i] >> 4) & 0x0F;

        EXPECT_EQ(low, h_input[i * 2]);
        if (i * 2 + 1 < N) {
            EXPECT_EQ(high, h_input[i * 2 + 1]);
        }
    }

    cuda_free(d_input);
    cuda_free(d_packed);
}
